import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClOfSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WordProd.OneBlockProd

theorem exists_equiv_tensor {α : Type} [Fintype α] [DecidableEq α] (X : α → Type) [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (i₀ : α) (hx : ∀ i, i ≠ i₀ → ∃ v : X i, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w) :
    ∃ (x : ∀ i, X i) (ι : X i₀ ≃ₗ[ℂ] ⨂[ℂ] i, X i),
      ∀ v, ι v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := by
  have hx' : ∀ i, ∃ (x : X i) (c : Module.Dual ℂ (X i)), i ≠ i₀ → c x = 1 ∧ ∀ w, c w • x = w := by
    intro i
    by_cases hi : i = i₀
    · exact ⟨0, 0, fun h => absurd hi h⟩
    · obtain ⟨v, hv, hs⟩ := hx i hi
      obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (X i), f v ≠ 0 := by
        by_contra h
        push Not at h
        exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
      refine ⟨v, (f v)⁻¹ • f, fun _ => ⟨by simp [hf], fun w => ?_⟩⟩
      obtain ⟨a, rfl⟩ := hs w
      simp [hf, mul_comm]
  choose x c hc using hx'
  let T : X i₀ →ₗ[ℂ] ⨂[ℂ] i, X i := (PiTensorProduct.tprod ℂ).toLinearMap x i₀
  have hT : ∀ v, T v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := fun v => rfl
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun v hv => ?_
    refine (Module.forall_dual_apply_eq_zero_iff ℂ v).1 fun l => ?_
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap
      (Function.update c i₀ l))) hv
    rw [hT, PiTensorProduct.lift.tprod, map_zero] at h1
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
    rw [Finset.prod_eq_single_of_mem i₀ (Finset.mem_univ _) (fun i _ hi => by
      rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact (hc i hi).1)] at h1
    simpa using h1
  have hsurj : Function.Surjective T := by
    intro y
    refine PiTensorProduct.induction_on y (fun r f => ?_) (fun y z hy hz => ?_)
    · let d : α → ℂ := fun i => if h : i = i₀ then 1 else c i (f i)
      have e1 : f = fun i => d i • Function.update x i₀ (f i₀) i := by
        funext i
        by_cases h : i₀ = i
        · subst h
          simp [d]
        · have h' : i ≠ i₀ := fun e => h e.symm
          simp only [d, dif_neg h', Function.update_of_ne h']
          exact ((hc i h').2 (f i)).symm
      have e2 : PiTensorProduct.tprod ℂ f =
          (∏ i, d i) • PiTensorProduct.tprod ℂ (Function.update x i₀ (f i₀)) := by
        rw [← MultilinearMap.map_smul_univ]
        exact congrArg _ e1
      exact ⟨r • (∏ i, d i) • f i₀, by rw [map_smul, map_smul, hT, e2]⟩
    · obtain ⟨u, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := hz
      exact ⟨u + v, map_add _ _ _⟩
  exact ⟨x, LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hirr : π.IsIrreducible) : ∃ v : V, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w := by
  have hg : ∀ g : G, g = 1 := fun g => Subsingleton.elim _ _
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊥ : Subrepresentation π) = ⊤ := by
      ext v; rw [h v]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by simpa [hg g] using hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  refine ⟨v, hv, fun w => ?_⟩
  have : w ∈ S := by rw [hS]; trivial
  exact Submodule.mem_span_singleton.1 this

theorem exists_conj_perm {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (e : n ≃ n) :
    ∃ w : GL n R, ∀ y : GL n R,
      ((w * y * w⁻¹ : GL n R) : Matrix n n R) = (y : Matrix n n R).submatrix e e := by
  let P : Matrix n n R := (1 : Matrix n n R).submatrix e (Equiv.refl n)
  let Q : Matrix n n R := (1 : Matrix n n R).submatrix (Equiv.refl n) e
  have hP : ∀ y : Matrix n n R, P * y = y.submatrix e (Equiv.refl n) := fun y => by
    ext s t
    simp [P, Matrix.mul_apply, Matrix.one_apply]
  have hQ : ∀ y : Matrix n n R, y * Q = y.submatrix (Equiv.refl n) e := fun y => by
    ext s t
    simp [Q, Matrix.mul_apply, Matrix.one_apply]
  have h1 : P * Q = 1 := by
    rw [hQ]
    ext s t
    simp [P, Matrix.one_apply]
  have h2 : Q * P = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨P, Q, h1, h2⟩, fun y => ?_⟩
  show P * (y : Matrix n n R) * Q = _
  rw [hQ, hP]
  rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_parInd {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W}
    {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (hP : ∀ g : GL n k, g ∈ parab k e)
    (hd : ∀ z, deltaHalf k m z = 1) (L : V ≃ₗ[ℂ] W)
    (law0 : ∀ (p : parab k e) v, ρ (leviProj k e p) (L v) = L (π p v)) :
    Nonempty (π.Equiv (parInd e ρ)) := by
  have law : ∀ (p : parab k e) v, twist ρ (deltaHalf k m) (leviProj k e p) (L v) = L (π p v) := fun p v => by
    simp only [twist_apply, hd, Units.val_one, one_smul, law0]
  let f : π.IntertwiningMap (parInd e ρ) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          refine Eq.trans ?_ (law p _).symm
          simp⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          simp [hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        simp)) }
  refine ⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩⟩
  · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) h
    simpa using h1
  · have h1 := φ.1.2 ⟨x, hP x⟩ 1
    rw [mul_one] at h1
    refine (law ⟨x, hP x⟩ _).symm.trans ?_
    rw [L.apply_symm_apply]
    exact h1.symm

theorem multiProd_single {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α)
    (h0 : ∀ i, i ≠ i₀ → b i = 0) (σ : ∀ i, IrrRep (GL (Fin (b i)) k))
    (g : (Σ i, Fin (b i)) ≃ Fin (b i₀)) :
    Nonempty ((multiProd g fun i => (σ i).ρ).Equiv (σ i₀).ρ) := by
  have hP : ∀ x : GL (Fin (b i₀)) k, x ∈ parab k g := fun x =>
    OneBlockCell.mem_parab_of_single g i₀ h0 x
  have hsub : ∀ i, i ≠ i₀ → Subsingleton (GL (Fin (b i)) k) := by
    intro i hi
    haveI : IsEmpty (Fin (b i)) := by rw [h0 i hi]; infer_instance
    exact ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨x, ι, hι⟩ := exists_equiv_tensor (fun i => (σ i).V) i₀ (fun i hi =>
    haveI := hsub i hi
    exists_line (σ i).ρ (σ i).irr)
  let E : Fin (b i₀) ≃ Fin (b i₀) := (OneBlockCell.valEquiv i₀ rfl h0).symm.trans g
  obtain ⟨w, hw⟩ := exists_conj_perm (R := k) E
  have hwp : ∀ p : parab k g, leviProj k g p i₀ = w * (p : GL (Fin (b i₀)) k) * w⁻¹ := fun p =>
    Units.ext (Matrix.ext fun s t => by
      rw [hw]
      rfl)
  let A : (σ i₀).V ≃ₗ[ℂ] (σ i₀).V := LinearEquiv.ofLinear ((σ i₀).ρ w) ((σ i₀).ρ w⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  obtain ⟨φ⟩ := nonempty_equiv_parInd (ρ := piTensor fun i => (σ i).ρ) (π := (σ i₀).ρ) g (σ i₀).smooth hP
    (OneBlockCell.deltaHalf_eq_one_of_single i₀ h0) (A.trans ι) (fun p v => by
      show (piTensor fun i => (σ i).ρ) (leviProj k g p) (ι ((σ i₀).ρ w v)) = ι ((σ i₀).ρ w ((σ i₀).ρ p v))
      rw [hι, hι, piTensor_tprod]
      refine congrArg _ (funext fun i => ?_)
      rw [Function.apply_update (fun i u => (σ i).ρ (leviProj k g p i) u)]
      by_cases h : i₀ = i
      · subst h
        rw [Function.update_self, Function.update_self, hwp, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel_right, map_mul, Module.End.mul_apply]
      · have h' : i ≠ i₀ := fun e => h e.symm
        haveI := hsub i h'
        rw [Function.update_of_ne h', Function.update_of_ne h',
          Subsingleton.elim (leviProj k g p i) 1, map_one]
        rfl)
  exact ⟨φ.symm⟩

theorem multiProd_clOf_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : IrrGL k) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α), b i₀ = a.1 → (∀ i, i ≠ i₀ → b i = 0) → ∀ (g : (Σ i, Fin (b i)) ≃ Fin a.1), Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) := by
  intro k _ _ _ _ a α _ _ b i₀ hb h0 g
  obtain ⟨N, c⟩ := a
  dsimp only at hb g ⊢
  subst hb
  obtain ⟨φ⟩ := multiProd_single b i₀ h0 (fun i => (clOf ⟨b i₀, c⟩ (b i)).rep) g
  have key : ∀ d : IrrCl (GL (Fin (b i₀)) k), d = c → Nonempty (d.rep.ρ.Equiv c.rep.ρ) := by
    rintro _ rfl
    exact ⟨.refl _⟩
  obtain ⟨ψ⟩ := key _ (clOf_self ⟨b i₀, c⟩)
  exact ⟨φ.trans ψ⟩

end GlobalTheory.CompanionTheory.WordProd.OneBlockProd

end
