import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible

open ReciprocityTheory.Ty.Fin CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.ProdSimple

def cf {Γ : Type} [Group Γ] (g : Γ) : MonoidAlgebra ℂ Γ →ₗ[ℂ] ℂ where
  toFun a := a.coeff g
  map_add' a b := by simp
  map_smul' r a := by simp

theorem cf_apply {Γ : Type} [Group Γ] (g : Γ) (a : MonoidAlgebra ℂ Γ) : cf g a = a.coeff g := rfl

def regSub {Γ : Type} [Group Γ] (N : Submodule ℂ (MonoidAlgebra ℂ Γ))
    (h : ∀ g : Γ, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N) : Representation ℂ Γ N where
  toFun g := (LinearMap.mulLeft ℂ (MonoidAlgebra.single g (1 : ℂ))).restrict (h g)
  map_one' := by
    ext a
    simp [← MonoidAlgebra.one_def]
  map_mul' g k := by
    refine LinearMap.ext fun a => Subtype.ext ?_
    change MonoidAlgebra.single (g * k) (1 : ℂ) * (a : MonoidAlgebra ℂ Γ) =
      MonoidAlgebra.single g (1 : ℂ) * (MonoidAlgebra.single k (1 : ℂ) * (a : MonoidAlgebra ℂ Γ))
    rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

theorem exists_irr {Γ : Type} [Group Γ] [Fintype Γ] {W : Type} [AddCommGroup W] [Module ℂ W]
    (T : MonoidAlgebra ℂ Γ →ₗ[ℂ] W) (hT : T 1 ≠ 0) :
    ∃ (N : Submodule ℂ (MonoidAlgebra ℂ Γ))
      (h : ∀ g : Γ, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
      IsIrr (regSub N h) ∧ ∃ n ∈ N, T n ≠ 0 := by
  classical
  have htop := IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)
  have hex : ∃ I : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ),
      IsSimpleModule (MonoidAlgebra ℂ Γ) I ∧ ∃ n ∈ I, T n ≠ 0 := by
    by_contra hno
    push Not at hno
    have hz : ∀ a ∈ sSup {m : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) |
        IsSimpleModule (MonoidAlgebra ℂ Γ) m}, T a = 0 := by
      intro a ha
      rw [sSup_eq_iSup'] at ha
      refine Submodule.iSup_induction _ (motive := fun x => T x = 0) ha ?_ (map_zero T) ?_
      · rintro ⟨I, hI⟩ x hx
        exact hno I hI x hx
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    exact hT (hz 1 (by rw [htop]; trivial))
  obtain ⟨I, hI, n, hn, hTn⟩ := hex
  have hstab : ∀ g : Γ, ∀ a ∈ I.restrictScalars ℂ,
      MonoidAlgebra.single g (1 : ℂ) * a ∈ I.restrictScalars ℂ := fun g a ha =>
    I.smul_mem (MonoidAlgebra.single g (1 : ℂ)) ha
  refine ⟨I.restrictScalars ℂ, hstab, ⟨?_, ?_⟩, n, hn, hTn⟩
  · have hn0 : n ≠ 0 := fun h0 => hTn (by rw [h0, map_zero])
    exact ⟨⟨⟨n, hn⟩, 0, fun h0 => hn0 (congrArg Subtype.val h0)⟩⟩
  · intro U hU

    have hmul : ∀ a : MonoidAlgebra ℂ Γ, ∀ x ∈ U.map (I.restrictScalars ℂ).subtype,
        a * x ∈ U.map (I.restrictScalars ℂ).subtype := by
      intro a
      induction a using MonoidAlgebra.induction_on with
      | of g =>
        rintro x ⟨u, hu, rfl⟩
        exact ⟨regSub _ hstab g u, hU g u hu, rfl⟩
      | add a b ha hb =>
        intro x hx
        rw [add_mul]
        exact Submodule.add_mem _ (ha x hx) (hb x hx)
      | smul r a ha =>
        intro x hx
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ r (ha x hx)
    let J : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) :=
      { carrier := U.map (I.restrictScalars ℂ).subtype
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun a x hx => hmul a x hx }
    have hJI : J ≤ I := by
      rintro x ⟨u, -, rfl⟩
      exact u.2
    rcases (isSimpleModule_iff_isAtom.mp hI).le_iff.mp hJI with h0 | h1
    · left
      rw [eq_bot_iff]
      intro u hu
      have : (u : MonoidAlgebra ℂ Γ) ∈ J := ⟨u, hu, rfl⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot _).1 this))
    · right
      rw [eq_top_iff]
      intro u _
      have : (u : MonoidAlgebra ℂ Γ) ∈ J := by
        rw [h1]
        exact u.2
      obtain ⟨u', hu', he⟩ := this
      have : u' = u := Subtype.ext he
      exact this ▸ hu'

variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def psi (ρ : Representation ℂ (∀ c, L c) W) (v : W) :
    MultilinearMap ℂ (fun c => MonoidAlgebra ℂ (L c)) W :=
  ∑ g : ∀ c, L c,
    ((MultilinearMap.mkPiAlgebra ℂ (Fin s) ℂ).compLinearMap (fun c => cf (g c))).smulRight (ρ g v)

theorem psi_apply (ρ : Representation ℂ (∀ c, L c) W) (v : W) (x : ∀ c, MonoidAlgebra ℂ (L c)) :
    psi ρ v x = ∑ g : ∀ c, L c, (∏ c, (x c).coeff (g c)) • ρ g v := by
  simp [psi, MultilinearMap.sum_apply, cf_apply]

theorem psi_one (ρ : Representation ℂ (∀ c, L c) W) (v : W) :
    psi ρ v (fun _ => 1) = v := by
  classical
  rw [psi_apply, Finset.sum_eq_single (1 : ∀ c, L c)]
  · simp [MonoidAlgebra.one_def]
  · intro g _ hg
    obtain ⟨c, hc⟩ : ∃ c, g c ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hg (funext hall)
    rw [Finset.prod_eq_zero (Finset.mem_univ c), zero_smul]
    simp [MonoidAlgebra.one_def, Finsupp.single_apply, hc.symm]
  · simp

theorem psi_single_mul (ρ : Representation ℂ (∀ c, L c) W) (v : W) (g : ∀ c, L c)
    (x : ∀ c, MonoidAlgebra ℂ (L c)) :
    psi ρ v (fun c => MonoidAlgebra.single (g c) (1 : ℂ) * x c) = ρ g (psi ρ v x) := by
  rw [psi_apply, psi_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => ?_
  simp only [MonoidAlgebra.coeff_single_mul_apply, one_mul, map_smul, Equiv.coe_mulLeft,
    Pi.mul_apply, Pi.inv_apply]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem exists_family (ρ : Representation ℂ (∀ c, L c) W) (v : W) (hv : v ≠ 0) :
    ∃ x : ∀ c, MonoidAlgebra ℂ (L c),
      (∀ c, ∃ (N : Submodule ℂ (MonoidAlgebra ℂ (L c)))
        (h : ∀ g : L c, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
        IsIrr (regSub N h) ∧ x c ∈ N) ∧ psi ρ v x ≠ 0 := by
  have key : ∀ S : Finset (Fin s), ∃ x : ∀ c, MonoidAlgebra ℂ (L c), (∀ c, c ∉ S → x c = 1) ∧
      (∀ c ∈ S, ∃ (N : Submodule ℂ (MonoidAlgebra ℂ (L c)))
        (h : ∀ g : L c, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
        IsIrr (regSub N h) ∧ x c ∈ N) ∧ psi ρ v x ≠ 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => 1, fun _ _ => rfl, by simp, by rwa [psi_one]⟩
    | insert c S hc ih =>
      obtain ⟨x, h1, h2, h3⟩ := ih
      have hT : (psi ρ v).toLinearMap x c 1 ≠ 0 := by
        rw [MultilinearMap.toLinearMap_apply, ← h1 c hc, Function.update_eq_self]
        exact h3
      obtain ⟨N, h, hirr, n, hn, hTn⟩ := exists_irr _ hT
      refine ⟨Function.update x c n, fun c' hc' => ?_, fun c' hc' => ?_, ?_⟩
      · rw [Finset.mem_insert, not_or] at hc'
        rw [Function.update_of_ne hc'.1]
        exact h1 c' hc'.2
      · by_cases hcc : c' = c
        · subst hcc
          exact ⟨N, h, hirr, by rwa [Function.update_self]⟩
        · obtain ⟨N', h', hirr', hm⟩ := h2 c' ((Finset.mem_insert.mp hc').resolve_left hcc)
          exact ⟨N', h', hirr', by rwa [Function.update_of_ne hcc]⟩
      · simpa [MultilinearMap.toLinearMap_apply] using hTn
  obtain ⟨x, -, h2, h3⟩ := key Finset.univ
  exact ⟨x, fun c => h2 c (Finset.mem_univ c), h3⟩

end GlobalTheory.CompanionTheory.ProdSimple

open GlobalTheory.CompanionTheory.ProdSimple in
theorem GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll : ReciprocityTheory.Ty.Fin.St.ProdSimpleAll := by
  intro s L _ _ W _ _ _ _ ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨x, hx, hne⟩ := exists_family ρ v hv
  choose N h hirr hmem using hx
  have hfin : ∀ c, Module.Finite ℂ (N c) := fun c => inferInstance
  let lam : ∀ c, FDRep ℂ (L c) := fun c => FDRep.of (regSub (N c) (h c))
  let M : MultilinearMap ℂ (fun c => (lam c : Type)) W :=
    (psi ρ v).compLinearMap (fun c => (N c).subtype)
  refine ⟨lam, PiTensorProduct.lift M, fun c => ?_, ?_, fun g => ?_⟩
  · exact (GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 (L c) (lam c)).2 (hirr c)
  · intro h0
    apply hne
    have := congrArg (fun f => f (PiTensorProduct.tprod ℂ (fun c => (⟨x c, hmem c⟩ : N c)))) h0
    simp only [LinearMap.zero_apply, PiTensorProduct.lift.tprod] at this
    exact this
  · apply PiTensorProduct.ext
    ext y
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      PiTensorProduct.lift.tprod]
    exact psi_single_mul ρ v g (fun c => (y c : MonoidAlgebra ℂ (L c)))
