import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPoly

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPolyPow

theorem aeval_mul_apply {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (p q : L[X]) (x : M) : Polynomial.aeval f (p * q) x = Polynomial.aeval f p (Polynomial.aeval f q x) := by
  rw [map_mul, Module.End.mul_apply]

theorem eigen_of_pow_of_separable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (c : L) (m : ℕ) (r : L[X]) (hr : r.Separable) (x : M)
    (h1 : Polynomial.aeval f ((X - C c) ^ m) x = 0) (h2 : Polynomial.aeval f r x = 0) :
    Polynomial.aeval f (X - C c) x = 0 := by
  obtain ⟨t, hrt, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr.ne_zero c
  have hle := Polynomial.rootMultiplicity_le_one_of_separable hr c
  have hcop : IsCoprime ((X - C c) ^ m) t :=
    ((Polynomial.irreducible_X_sub_C c).coprime_iff_not_dvd.2 hnd).pow_left
  obtain ⟨A, B', hAB⟩ := hcop
  have hs : ∃ s : L[X], (X - C c) * t = s * r := by
    interval_cases hj : r.rootMultiplicity c
    · exact ⟨X - C c, by rw [hrt]; ring⟩
    · exact ⟨1, by rw [hrt]; ring⟩
  obtain ⟨s, hs⟩ := hs
  have : (X - C c) = (A * (X - C c)) * (X - C c) ^ m + (B' * s) * r := by
    rw [mul_assoc (B') s r, ← hs]
    linear_combination (-(X - C c)) * hAB
  rw [this, map_add, LinearMap.add_apply, aeval_mul_apply, h1, map_zero, aeval_mul_apply, h2, map_zero, add_zero]

theorem mem_iSup_eigen_pow {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (r : L[X]) (hr : r.Separable)
    (hrD : ∀ x ∈ D, Polynomial.aeval f r x = 0) (c : ι → L) (m : ℕ) (s : Finset ι) :
    (∀ a ∈ s, ∀ b ∈ s, c a = c b → a = b) → ∀ d ∈ D,
      Polynomial.aeval f ((∏ a ∈ s, (X - C (c a))) ^ m) d = 0 →
      d ∈ ⨆ a ∈ s, (D ⊓ LinearMap.ker (f - c a • LinearMap.id)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ d _ h
    simp at h
    simp [h]
  | insert a t hat ih =>
    intro hinj d hd h
    rw [Finset.prod_insert hat, mul_pow] at h
    have hcop : IsCoprime ((X - C (c a)) ^ m) ((∏ b ∈ t, (X - C (c b))) ^ m) := by
      refine IsCoprime.pow (IsCoprime.prod_right fun b hb => ?_)
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 fun e => hat ?_))
      rw [hinj a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) e]
      exact hb
    obtain ⟨u, v, huv⟩ := hcop
    set Q := (∏ b ∈ t, (X - C (c b))) ^ m with hQ
    have hdec : d = Polynomial.aeval f (u * (X - C (c a)) ^ m) d + Polynomial.aeval f (v * Q) d := by
      rw [← LinearMap.add_apply, ← map_add, huv, map_one, Module.End.one_apply]
    rw [Finset.iSup_insert, hdec, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · have hmem := GlobalTheory.PassPoly.aeval_mem_of_stable f D hD (v * Q) d hd
      refine ⟨hmem, ?_⟩
      have h1 : Polynomial.aeval f ((X - C (c a)) ^ m) (Polynomial.aeval f (v * Q) d) = 0 := by
        rw [← aeval_mul_apply, show (X - C (c a)) ^ m * (v * Q) = v * ((X - C (c a)) ^ m * Q) by ring,
          aeval_mul_apply, h, map_zero]
      have := eigen_of_pow_of_separable f (c a) m r hr _ h1 (hrD _ hmem)
      simpa [Module.algebraMap_end_apply] using this
    · refine ih (fun x hx y hy => hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)) _
        (GlobalTheory.PassPoly.aeval_mem_of_stable f D hD _ d hd) ?_
      rw [← aeval_mul_apply, show Q * (u * (X - C (c a)) ^ m) = u * ((X - C (c a)) ^ m * Q) by ring,
        aeval_mul_apply, h, map_zero]

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_pow (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    (actVB PC.PD ρ g ^ n) x = actVB PC.PD ρ (g ^ n) x := by
  induction n generalizing x with
  | zero => simp [GlobalTheory.PassPoly.actVB_one']
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, GlobalTheory.PassPoly.actVB_mul']

theorem aeval_index_kill (g : G) : ∀ x ∈ PC.Dpcris ρ,
    Polynomial.aeval (actVB PC.PD ρ g) (X ^ PC.H.index - C (1 : LL)) x = 0 := by
  intro x hx
  haveI := PC.normal
  have hg : g ^ PC.H.index ∈ PC.H := Subgroup.pow_index_mem PC.H g
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply]
  rw [actVB_pow, (GlobalTheory.PassPoly.mem_Dpcris_iff PC ρ x).1 hx _ hg, sub_self]

theorem separable_index [CharZero LL] : (X ^ PC.H.index - C (1 : LL)).Separable := by
  haveI := PC.finiteIndex
  exact Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero) one_ne_zero

theorem inertiaThrough_of_poly_pow [CharZero LL] (Sig : Finset (PC.Iner →* LLˣ))
    (h1 : ∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1)
    (h2 : ∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p)
    (h3 : ∀ (g : PC.Iner), ∃ m : ℕ, ∀ d ∈ PC.Dpcris ρ, (Polynomial.aeval (actVB PC.PD ρ (g : G))
      ((∏ a ∈ Sig, (X - C ((a g : LLˣ) : LL))) ^ m)) d = 0)
    (h4 : ∃ γ : PC.Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧
      ∀ g : PC.Iner, ∃ (n : ℕ) (u : PC.Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) :
    PC.InertiaThrough ρ Sig := by

  have htriv : ∀ u : PC.Iner, (∀ a ∈ Sig, a u = 1) → ∀ x ∈ PC.Dpcris ρ,
      actVB PC.PD ρ (u : G) x = x := by
    intro u hu x hx
    obtain ⟨m, hm⟩ := h3 u
    have hprod : (∏ a ∈ Sig, (X - C ((a u : LLˣ) : LL))) ^ m = (X - C (1 : LL)) ^ (Sig.card * m) := by
      rw [Finset.prod_congr rfl (fun a ha => by rw [hu a ha, Units.val_one]), Finset.prod_const, pow_mul]
    have hk := hm x hx
    rw [hprod] at hk
    have := eigen_of_pow_of_separable _ 1 _ _ (separable_index PC) x hk (aeval_index_kill PC ρ _ x hx)
    simpa [Module.algebraMap_end_apply, sub_eq_zero] using this
  refine ⟨h1, h2, le_antisymm ?_ ?_⟩
  · obtain ⟨γ, hsep, hgen⟩ := h4
    intro d hd
    obtain ⟨m, hm⟩ := h3 γ
    have := mem_iSup_eigen_pow (actVB PC.PD ρ (γ : G)) (PC.Dpcris ρ) (GlobalTheory.PassPoly.Dpcris_stable PC ρ γ)
      _ (separable_index PC) (aeval_index_kill PC ρ _)
      (fun a : PC.Iner →* LLˣ => ((a γ : LLˣ) : LL)) m Sig
      (fun a ha b hb e => hsep a ha b hb (Units.ext e)) d hd (hm d hd)
    refine (iSup₂_mono (fun a ha => ?_) : _ ≤ ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) this
    rintro x ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have hγ : actVB PC.PD ρ (γ : G) x = ((a γ : LLˣ) : LL) • x := by
      simpa [sub_eq_zero] using hx'
    have hn : ∀ n : ℕ, actVB PC.PD ρ ((γ : G) ^ n) x = ((a γ : LLˣ) : LL) ^ n • x := by
      intro n
      induction n with
      | zero => simp [GlobalTheory.PassPoly.actVB_one']
      | succ n ih => rw [pow_succ, GlobalTheory.PassPoly.actVB_mul', hγ, map_smul, ih, smul_smul, pow_succ, mul_comm]
    simp only [Submodule.coe_iInf, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro g
    obtain ⟨n, u, hu, rfl⟩ := hgen g
    rw [map_mul, hu a ha, mul_one, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, GlobalTheory.PassPoly.actVB_mul',
      htriv u hu x hx, hn, Units.val_pow_eq_pow_val]
  · exact iSup₂_le fun a _ => inf_le_left

end

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) l) → (∀ (g : (pc P h hN hF hS).Iner), ∃ m : ℕ, ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, (Polynomial.aeval (actVB (P.PD K) ρ (g : ↥(GK K))) ((∏ a ∈ Sig, (X - C ((a g : (↥LL.1)ˣ) : ↥LL.1))) ^ m)) d = 0) → (∃ γ : (pc P h hN hF hS).Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) → (pc P h hN hF hS).InertiaThrough ρ Sig := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ Sig h1 h2 h3 h4
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  refine inertiaThrough_of_poly_pow (pc P h hN hF hS) ρ Sig h1 ?_ h3 h4
  have hp : (pc P h hN hF hS).PD.p = l := P.PD_p K
  rw [hp]
  exact h2

end GlobalTheory.PassPolyPow

end
