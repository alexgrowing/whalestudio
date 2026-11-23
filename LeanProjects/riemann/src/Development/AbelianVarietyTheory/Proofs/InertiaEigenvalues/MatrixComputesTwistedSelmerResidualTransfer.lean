import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearCoefficientMapCocycles

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.ResSel.CoefMap

namespace GlobalTheory.ResSel.Transfer

section Alg

variable {O Λ K : Type} [CommRing O] [CommRing Λ] [CommRing K] [Algebra O Λ] [Algebra O K] [Module Λ K]
  (φ : Λ →ₐ[O] K) (hs : ∀ (y : Λ) (b : K), y • b = φ y * b)

def idVec (r : ℕ) : (Fin r → K) →ₛₗ[(φ : Λ →+* K)] (Fin r → K) where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := funext fun a => hs c (m a)

include hs in
theorem matAct_eq {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ) (x : Fin n → K) :
    matAct (M := K) Φ x = (Φ.map φ).mulVec x := by
  funext a
  simp [matAct, hs, Matrix.mulVec, dotProduct]

include hs in
theorem repOn_eq {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (g : Γ) (m : Fin r → K) :
    repOn ρ κ K g m = φ ((κ g : Λˣ) : Λ) • ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O K)).mulVec m := by
  funext a
  simp [repOn, matAct, hs, Matrix.mulVec, dotProduct]

theorem idVec_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
    (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1) (g : Γ) (m : Fin r → K) :
    idVec φ hs r (repOn ρ κ K g m) = repOn ρ (1 : Γ →* Kˣ) K g (idVec φ hs r m) := by
  change repOn ρ κ K g m = repOn ρ (1 : Γ →* Kˣ) K g m
  rw [repOn_eq φ hs, hκ]
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

variable [TopologicalSpace K] [DiscreteTopology K] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {r : ℕ}
  (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1)

def tau : H1 (repOn ρ κ K) →ₛₗ[(φ : Λ →+* K)] H1 (repOn ρ (1 : Γ →* Kˣ) K) :=
  slH1 _ _ (idVec φ hs r) continuous_of_discreteTopology (idVec_repOn φ hs ρ κ hκ)

theorem tau_injective : Function.Injective (tau φ hs ρ κ hκ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles _ _ (idVec φ hs r) continuous_of_discreteTopology
      (idVec_repOn φ hs ρ κ hκ) z) : H1 (repOn ρ (1 : Γ →* Kˣ) K)) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
    refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    have e : repOn ρ κ K g m = repOn ρ (1 : Γ →* Kˣ) K g m := idVec_repOn φ hs ρ κ hκ g m
    rw [e]
    exact hm g

def kerIn {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ) (x : LinearMap.ker (Φ.map φ).mulVecLin) :
    LinearMap.ker (matAct (M := K) Φ) :=
  ⟨x.1, by rw [LinearMap.mem_ker, matAct_eq φ hs]; exact x.2⟩

theorem exists_linear (hsurj : Function.Surjective (algebraMap O K)) {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ)
    (S : Submodule Λ (H1 (repOn ρ κ K))) (e : LinearMap.ker (matAct (M := K) Φ) ≃ₗ[Λ] S) :
    ∃ E : LinearMap.ker (Φ.map φ).mulVecLin →ₗ[K] H1 (repOn ρ (1 : Γ →* Kˣ) K), Function.Injective E ∧
      ∀ x, E x = tau φ hs ρ κ hκ (e (kerIn φ hs Φ x)).1 := by
  refine ⟨{ toFun := fun x => tau φ hs ρ κ hκ (e (kerIn φ hs Φ x)).1
            map_add' := fun x y => ?_
            map_smul' := fun c x => ?_ }, fun x y hxy => ?_, fun _ => rfl⟩
  · rw [show kerIn φ hs Φ (x + y) = kerIn φ hs Φ x + kerIn φ hs Φ y from rfl, map_add, Submodule.coe_add, map_add]
  · obtain ⟨o, rfl⟩ := hsurj c
    have h1 : kerIn φ hs Φ (algebraMap O K o • x) = algebraMap O Λ o • kerIn φ hs Φ x := by
      apply Subtype.ext
      funext b
      change algebraMap O K o * x.1 b = algebraMap O Λ o • x.1 b
      rw [hs, AlgHom.commutes]
    rw [h1, map_smul, Submodule.coe_smul, map_smulₛₗ, RingHom.id_apply]
    congr 1
    exact φ.commutes o
  · have h1 := e.injective (Subtype.ext (tau_injective φ hs ρ κ hκ hxy))
    have h2 : (kerIn φ hs Φ x).1 = (kerIn φ hs Φ y).1 := congrArg Subtype.val h1
    exact Subtype.ext h2

end Alg

section Sel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {Λ K : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing K] [Algebra (X.O0 i) K] [Module Λ K]
  [TopologicalSpace K] [DiscreteTopology K]
  (φ : Λ →ₐ[X.O0 i] K) (hs : ∀ (y : Λ) (b : K), y • b = φ y * b) (κ : GE N →* Λˣ) (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1)

theorem tau_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ K v) :
    slH1 ((repOn ρ κ K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype)
      (idVec φ hs r) continuous_of_discreteTopology (fun g m => idVec_repOn φ hs ρ κ hκ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idVec φ hs r) continuous_of_discreteTopology
        (fun g m => idVec_repOn φ hs ρ κ hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩
      change ((z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, smul_eq_mul, hs, AlgHom.commutes]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem tau_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ K)) (hx : x ∈ selOn bkP i ρ κ K Q) :
    tau φ hs ρ κ hκ x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_slH1 (repOn ρ κ K) (repOn ρ (1 : GE N →* Kˣ) K) (idVec φ hs r) continuous_of_discreteTopology
    (idVec_repOn φ hs ρ κ hκ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact tau_mem_bkOn bkP i ρ φ hs κ hκ v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

end Sel

theorem tors_of_cast_eq_zero {B : Type} [CommRing B] {l : ℕ} (h : (l : B) = 0) (b : B) : ∃ n : ℕ, (l ^ n) • b = 0 :=
  ⟨1, by rw [pow_one, nsmul_eq_mul, h, zero_mul]⟩

theorem computes_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k], ((X.l i : ℕ) : k) = 0 → Function.Surjective (algebraMap (X.O0 i) k) → ∀ aug : abelian₂ X i M ι →ₐ[X.O0 i] k, (∀ δ, aug (MonoidAlgebra.of (X.O0 i) (Del X i M ι) δ) = 1) → ∃ E : LinearMap.ker (Φ.map aug).mulVecLin →ₗ[k] H1 (red i k (Tgl i s)), Function.Injective E ∧ (∀ x, E x ∈ selOn bkP i (Tgl i s) (1 : GE N →* kˣ) k Q) ∧ ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (th : abelian₂ X i M ι →ₐ[X.O0 i] B), ((X.l i : ℕ) : B) = 0 → ∀ x : Fin a → B, (Φ.map th).mulVec x = 0 → ∃ z : GE N → Fin D.R.r → B, IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + th ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) • ((Tmat i s g).map (algebraMap (X.O0 i) B)).mulVec (z h)) ∧ ∀ f : B →+ k, (∀ y b, f (th y * b) = aug y * f b) → ∃ (x' : LinearMap.ker (Φ.map aug).mulVecLin) (z' : Z1 (red i k (Tgl i s))), (∀ c, x'.1 c = f (x c)) ∧ (∀ g c, z'.1 g c = f (z g c)) ∧ E x' = cl z' := by
  intro D N X bkP i s M ι d Q a Φ hC k _ _ _ _ hk hsurj aug haug
  obtain ⟨e, he⟩ := hC
  letI : Module (abelian₂ X i M ι) k := Module.compHom k (aug : abelian₂ X i M ι →+* k)
  have hs : ∀ (y : abelian₂ X i M ι) (b : k), y • b = aug y * b := fun _ _ => rfl
  have hκ : ∀ g, aug ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) = 1 := fun g =>
    haug (delAll X i M d g)⁻¹
  have hkT := tors_of_cast_eq_zero hk
  obtain ⟨E, hEi, hE⟩ := exists_linear aug hs (Tgl i s) (delInv i M d) hκ hsurj Φ _ (e k hkT)
  refine ⟨E, hEi, fun x => ?_, ?_⟩
  · rw [hE]
    exact tau_mem_selOn bkP i _ aug hs _ hκ Q _ (e k hkT (kerIn aug hs Φ x)).2
  intro B _ _ th hB x hx
  letI : Module (abelian₂ X i M ι) B := Module.compHom B (th : abelian₂ X i M ι →+* B)
  have hsB : ∀ (y : abelian₂ X i M ι) (b : B), y • b = th y * b := fun _ _ => rfl
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hBT := tors_of_cast_eq_zero hB
  let xB : LinearMap.ker (matAct (M := B) Φ) := ⟨x, by rw [LinearMap.mem_ker, matAct_eq th hsB]; exact hx⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e B hBT xB).1
  refine ⟨z.1, (IsLocallyConstant.iff_continuous _).2 z.2.1, fun g h => ?_, fun f hf => ?_⟩
  · rw [z.2.2 g h, repOn_eq th hsB, Tgl_coe]
  let fl : B →ₗ[abelian₂ X i M ι] k :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun y b => hf y b }
  have hx' : (Φ.map aug).mulVec (fun c => f (x c)) = 0 := by
    funext c
    have h1 := congrArg f (congrFun hx c)
    simpa [Matrix.mulVec, dotProduct, map_sum, hf] using h1
  let z₁ : Z1 (repOn (Tgl i s) (delInv i M d) k) :=
    cocycles1MapOfEquivariant _ _ (fl.compLeft (Fin D.R.r)) continuous_of_discreteTopology (repOn_map (Tgl i s) (delInv i M d) fl) z
  refine ⟨⟨fun c => f (x c), hx'⟩, semilinearCoefficientMapCocycles _ _ (idVec aug hs D.R.r) continuous_of_discreteTopology
    (idVec_repOn aug hs (Tgl i s) (delInv i M d) hκ) z₁, fun _ => rfl, fun _ _ => rfl, ?_⟩
  rw [hE, he B k hBT hkT fl xB (kerIn aug hs Φ ⟨fun c => f (x c), hx'⟩) z z₁ (fun _ => rfl) (fun _ _ => rfl) hz.symm]
  rfl

end GlobalTheory.ResSel.Transfer

end
