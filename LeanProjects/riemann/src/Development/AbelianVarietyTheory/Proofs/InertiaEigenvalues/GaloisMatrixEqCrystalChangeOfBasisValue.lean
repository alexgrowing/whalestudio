import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysGalValue

section Algebra

variable {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  {f : A →+* B} {u : M →ₛₗ[f] N}

theorem span_range_eq_top (h : SemiBC u) : Submodule.span B (Set.range u) = ⊤ := by
  obtain ⟨w, -, hw⟩ := h (N ⧸ Submodule.span B (Set.range u)) 0
  have h1 := hw (Submodule.mkQ _) fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨x, rfl⟩)
  have h2 := hw 0 fun _ => rfl
  rw [← Submodule.ker_mkQ (Submodule.span B (Set.range u)), h1, ← h2, LinearMap.ker_zero]

theorem induction_bc (h : SemiBC u) (p : N → Prop) (h0 : ∀ x, p (u x)) (h1 : ∀ y z, p y → p z → p (y + z))
    (h2 : ∀ (b : B) y, p y → p (b • y)) (y : N) : p y := by
  have hy : y ∈ Submodule.span B (Set.range u) := by rw [span_range_eq_top h]; trivial
  induction hy using Submodule.span_induction with
  | mem _ hx => obtain ⟨x, rfl⟩ := hx; exact h0 x
  | zero => rw [← map_zero u]; exact h0 0
  | add y z _ _ hy hz => exact h1 y z hy hz
  | smul b y _ hy => exact h2 b y hy

variable {R S ι : Type} [CommRing R] [CommRing S]

theorem exists_coord (h : SemiBC u) (π : R →+* S) (hπ : Function.Injective π) (i : B → R) (J : N →+ (ι → S))
    (hJ : ∀ (b : B) y, J (b • y) = π (i b) • J y) (h0 : ∀ x, ∃ c : ι → R, (fun k => π (c k)) = J (u x)) :
    ∃ κ : N →+ (ι → R), ∀ y, (fun k => π (κ y k)) = J y := by
  have key : ∀ y, ∃ c : ι → R, (fun k => π (c k)) = J y := induction_bc h _ h0
    (fun y z ⟨c, hc⟩ ⟨d, hd⟩ => ⟨c + d, by rw [map_add, ← hc, ← hd]; exact funext fun k => map_add π _ _⟩)
    (fun b y ⟨c, hc⟩ => ⟨i b • c, by rw [hJ, ← hc]; exact funext fun k => map_mul π _ _⟩)
  choose κ hκ using key
  refine ⟨AddMonoidHom.mk' κ fun y z => funext fun k => hπ ?_, hκ⟩
  rw [Pi.add_apply, map_add, congrFun (hκ _) k, congrFun (hκ _) k, congrFun (hκ _) k, map_add, Pi.add_apply]

theorem exists_ext (h : SemiBC u) (π : R →+* S) (i : A → R) (ψ : B →+* S) (hi : ∀ a, π (i a) = ψ (f a))
    (κ : M →+ (ι → R)) (hκ : ∀ (a : A) x, κ (a • x) = i a • κ x) :
    ∃ w : N →+ (ι → S), (∀ (b : B) y, w (b • y) = ψ b • w y) ∧ (∀ x k, w (u x) k = π (κ x k)) ∧
      ∀ (U : M → M) (U' : N →ₗ[B] N) (r : R), (∀ x, U' (u x) = u (U x)) → (∀ x, κ (U x) = r • κ x) →
        ∀ y, w (U' y) = π r • w y := by
  letI : Module B (ι → S) := Module.compHom _ ψ
  obtain ⟨w, hw, -⟩ := h (ι → S)
    { toFun := fun x k => π (κ x k)
      map_add' := fun x y => funext fun k => by rw [map_add, Pi.add_apply, map_add]; rfl
      map_smul' := fun a x => funext fun k => by
        rw [hκ, Pi.smul_apply, smul_eq_mul, map_mul, hi]; rfl }
  have hs : ∀ (b : B) y, w (b • y) = ψ b • w y := fun b y => w.map_smul b y
  refine ⟨w.toAddMonoidHom, hs, fun x k => congrFun (hw x) k, fun U U' r h1 h2 => ?_⟩
  refine induction_bc h (fun y => w (U' y) = π r • w y) (fun x => ?_) (fun y z hy hz => ?_) fun b y hy => ?_
  · rw [h1, hw, hw]
    funext k
    change π (κ (U x) k) = π r * π (κ x k)
    rw [h2, Pi.smul_apply, smul_eq_mul, map_mul]
  · simp only [map_add, smul_add, hy, hz]
  · rw [U'.map_smul, hs, hs, hy, smul_comm]

end Algebra

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

theorem toW_bas (j : ι) (hm : (bas j : Vec K a ι) ∈ ME P) : toW t ϖ P ⟨bas j, hm⟩ = Pi.single j 1 := by
  funext i
  rw [toW_apply]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, ← map_one (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (Pi.single_eq_same (M := fun _ : ι => K⟦X⟧) i 1))
  · rw [Pi.single_eq_of_ne h, ← map_zero (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (Pi.single_eq_of_ne (M := fun _ : ι => K⟦X⟧) h 1))

theorem isLMat_of_single (I : Ident t ϖ P T) (s : GQ l) (g : G) (γ : ι → ι → OA l O)
    (h : ∀ j, I.act s g (Pi.single j 1) = fun i => inclO l O (γ j i)) :
    I.IsLMat s g (Matrix.of fun i j => frobOA l O (γ j i)) := fun c => by
  have h1 : inclL t ϖ P c = ∑ j, inclO l O (c j) • phiW t ϖ P (Pi.single j 1) := by
    funext i
    simp [inclL_apply, phiW_apply, Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite (frobOW l O), mul_comm]
  rw [h1, map_sum]
  simp only [I.act_smul, I.act_phiW, h, galOW_inclO]
  simp only [phiW_apply, frobOW_inclO, inclL_apply]
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum,
    map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem kappa_act (T : LocLat G ℚ_[l] K O) (s : GQ l) (g : G) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (TensorProduct.map (galW l s).toLinearMap (actZ T g) y) =
      TWact (galOW O s) T g (kappa T y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem value_eq {l : ℕ} {R₀ O R S ι Q : Type} [CommRing R₀] [CommRing O] [CommRing R] [CommRing S] [Algebra O R]
    [Algebra O S] [Fintype ι] [DecidableEq ι] [Fintype Q] (E : FCrys l R₀) {P₀ P₁ PP Cr : Obj l R₀}
    (oE : O → FHom E E) (b : ι → E.M P₀) (α : GlobalTheory.Prism.Hom P₀ P₁) (σ : GlobalTheory.Prism.Hom P₁ P₁)
    (p₀ p₁ : GlobalTheory.Prism.Hom P₀ PP) (h : GlobalTheory.Prism.Hom P₁ Cr) (ev : GlobalTheory.Prism.Hom PP Cr)
    (h₀ : ev.comp p₀ = h.comp α) (h₁ : ev.comp p₁ = (h.comp σ).comp α) (c : ι → ι → Q → O)
    (y : ι → ι → Q → PP.A) (hy : ∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i)))
    (π : R →ₐ[O] S) (ν : P₁.A → R) (ψ : Cr.A →+* S) (hν : ∀ w, π (ν w) = ψ (h.f w)) (κ : E.M P₁ →+ (ι → R))
    (hκs : ∀ (w : P₁.A) x, κ (w • x) = ν w • κ x) (hκo : ∀ (o : O) x, κ ((oE o).u _ x) = o • κ x)
    (hκb : ∀ j, κ (E.tr α (b j)) = Pi.single j 1) (i j : ι) :
    π (κ (E.tr σ (E.tr α (b j))) i) = ∑ q, c i j q • ψ (ev.f (y i j q)) := by
  obtain ⟨w, hws, hwu, hwo⟩ := exists_ext (E.tr_bc h) π.toRingHom ν ψ hν κ hκs
  have hwo' : ∀ (o : O) z, w ((oE o).u Cr z) = o • w z := fun o z =>
    (hwo _ ((oE o).u Cr) (algebraMap O R o) ((oE o).u_tr h)
      (fun x => (hκo o x).trans (algebraMap_smul _ _ _).symm) z).trans
      ((congrArg (· • w z) (π.commutes o)).trans (algebraMap_smul _ _ _))
  have hwb : ∀ i k, w (E.tr ev (E.tr p₀ (b i))) k = if k = i then 1 else 0 := fun i k => by
    rw [← E.tr_comp, h₀, E.tr_comp, hwu, hκb, Pi.single_apply, apply_ite π.toRingHom, map_one, map_zero]
  refine (hwu _ i).symm.trans ?_
  have h2 := congrArg (E.tr ev) (hy j)
  rw [← E.tr_comp, h₁, E.tr_comp, E.tr_comp] at h2
  rw [h2]
  simp only [map_sum, LinearMap.map_smulₛₗ, ← FHom.u_tr, hws, hwo',
    Finset.sum_apply, Pi.smul_apply, hwb]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [if_pos rfl, smul_comm, smul_eq_mul, mul_one]

theorem exists_coord' {A B M N O R S ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} [CommRing O] [CommRing R] [CommRing S]
    [Algebra O R] [Algebra O S] [DecidableEq ι] (h : SemiBC u) (π : R →ₐ[O] S) (hπ : Function.Injective π)
    (ν : B → R) (J : N →+ (ι → S)) (hJ : ∀ (b : B) y, J (b • y) = π (ν b) • J y)
    (h0 : ∀ x, ∃ c : ι → R, (fun k => π (c k)) = J (u x)) :
    ∃ κ : N →+ (ι → R), (∀ y, (fun k => π (κ y k)) = J y) ∧ (∀ (b : B) y, κ (b • y) = ν b • κ y) ∧
      (∀ (o : O) y z, J z = o • J y → κ z = o • κ y) ∧ ∀ j y, J y = Pi.single j 1 → κ y = Pi.single j 1 := by
  obtain ⟨κ, hκ⟩ := exists_coord h π.toRingHom hπ ν J hJ h0
  have hκ' : ∀ x k, π (κ x k) = J x k := fun x k => congrFun (hκ x) k
  refine ⟨κ, hκ, fun b y => funext fun k => hπ ?_, fun o y z h1 => funext fun k => hπ ?_,
    fun j y h1 => funext fun k => hπ ?_⟩
  · rw [hκ', hJ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hκ']
  · rw [hκ', h1, Pi.smul_apply, Pi.smul_apply, map_smul, hκ']
  · rw [hκ', h1, Pi.single_apply, Pi.single_apply, apply_ite π, map_one, map_zero]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP), ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ (g : ↥(GK (ϖ.field a))) (ev : GlobalTheory.Prism.Hom PP Cr), ev.comp p₀ = h.comp (ϖ.toAinf a) → ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) → ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ i j, toOCr l O (Γ i j) = ∑ q, c i j q ⊗ₜ[ℤ_[l]] eC (ev.f (y i j q)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE b hb PP p₀ p₁ Q _ c y hy Cr eC h hh g ev h₀ h₁
  have hJ0 : ∃ J : E.M (ainfObj (ϖ.field a)) →+ (ι → OW l O), ∀ x, I.j (J x) = kappa T (jA x) :=
    ⟨I.j.symm.toAddMonoidHom.comp ((kappa T).comp jA.toAddMonoidHom), fun x => I.j.apply_symm_apply _⟩
  obtain ⟨J, hJ⟩ := hJ0
  have hJs : ∀ (w : (ainfObj (ϖ.field a)).A) x,
      J (w • x) = inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfId (ϖ.field a) w) • J x := fun w x => I.j.injective (by
    rw [map_smul I.j, hJ, hJ]
    exact (congrArg (kappa T) (jA.map_smulₛₗ w x)).trans (OfCrystal.kappa_smul T _ _))
  have hJo : ∀ (o : O) x, J ((oE o).u _ x) = o • J x := fun o x => I.j.injective (by
    rw [LinearMapClass.map_smul_of_tower, hJ, hJ, hoE, OfCrystal.kappa_mulZ])
  have hJb : ∀ j, J (E.tr (ϖ.toAinf a) (b j)) = Pi.single j 1 := fun j => I.j.injective (by
    obtain ⟨hm, h1⟩ := hb j
    rw [hJ, h1, toW_bas])
  have hJg : ∀ x, J (E.tr (ainfHom (ϖ.field a) g) x) = I.act (g : GQ l) g (J x) := fun x => I.j.injective (by
    rw [I.j_act, hJ, hJ]
    exact (congrArg (kappa T) (H.j_act g x)).trans (kappa_act T _ _ _))
  have hκ0 := exists_coord' (E.tr_bc (ϖ.toAinf a)) (inclO l O) inclO_injective
    (fun w => (1 : O) ⊗ₜ[ℤ_[l]] ainfId (ϖ.field a) w) J hJs fun x => by
      obtain ⟨m, hm, h1⟩ := (him _).1 ⟨x, rfl⟩
      rw [I.j.injective ((hJ _).trans h1)]
      exact toW_mem_MA t ϖ P hm
  obtain ⟨κ, hκ, hκs, hκo, hκb⟩ := hκ0
  refine ⟨_, isLMat_of_single I _ g
    (fun j => κ (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) (b j)))) fun j => ?_, fun i j => ?_⟩
  · exact (congrArg (I.act (g : GQ l) g) (hJb j).symm).trans ((hJg _).symm.trans (hκ _).symm)
  · refine (value_eq E oE b _ _ p₀ p₁ h ev h₀ h₁ c y hy ((toOCr l O).comp (frobOA l O)) _
      ((Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O).toRingHom.comp eC.toRingHom)
      (fun w => (congrArg (toOCr l O) (frobOA_tmul 1 w)).trans
        (congrArg (fun z : Per.Acris l => (1 : O) ⊗ₜ[ℤ_[l]] z) (hh w).symm)) κ hκs
      (fun o x => hκo o _ _ (hJo o x)) (fun k => hκb k _ (hJb k)) i j).trans
      (Finset.sum_congr rfl fun q _ => ?_)
    exact congrArg (fun o : O => o ⊗ₜ[ℤ_[l]] eC (ev.f (y i j q))) (mul_one (c i j q))

end GlobalTheory.CrysGalValue
