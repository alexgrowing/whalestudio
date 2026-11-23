import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvectorMemOfSumMem

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory

theorem subIner_component_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ g, ∀ y ∈ U, T g y ∈ U) (S : Finset α) :
    ∀ y : α → Y, (∀ a ∈ S, ∀ g, T g (y a) = χ a g • y a) → ∑ a ∈ S, y a ∈ U → ∀ a ∈ S, y a ∈ U := by
  first
  | exact @_root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem
  | exact _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem
  | (apply _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem ..)

theorem subIner_pullback {L X Y I α J : Type} [Field L] [AddCommGroup X] [Module L X]
    [AddCommGroup Y] [Module L Y] (T : I → X →ₗ[L] X) (T' : J → I → Y →ₗ[L] Y)
    (m : J → X →ₗ[L] Y) (hm : ∀ j g x, m j (T g x) = T' j g (m j x))
    (hinj : ∀ x, (∀ j, m j x = 0) → x = 0)
    (χ : α → I → L) (hχ : Function.Injective χ) (D : Submodule L X)
    (hD : ∀ g, ∀ x ∈ D, T g x ∈ D) (S : Finset α) (d : X) (hd : d ∈ D)
    (y : J → α → Y) (hy : ∀ j, ∀ a ∈ S, ∀ g, T' j g (y j a) = χ a g • y j a)
    (hs : ∀ j, ∑ a ∈ S, y j a = m j d) :
    ∃ x : α → X, (∀ a ∈ S, x a ∈ D ∧ ∀ g, T g (x a) = χ a g • x a) ∧ ∑ a ∈ S, x a = d := by
  classical
  have key := subIner_component_mem (Y := J → Y)
    (fun g => LinearMap.pi fun j => (T' j g).comp (LinearMap.proj j)) χ hχ (D.map (LinearMap.pi m))
    (by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨T g x, hD g x hx, by ext j; simp [hm]⟩) S (fun a j => y j a)
    (fun a ha g => by ext j; simp [hy j a ha g])
    ⟨d, hd, by ext j; simp [← hs j, Finset.sum_apply]⟩
  have h1 : ∀ a, ∃ x : X, a ∈ S → x ∈ D ∧ ∀ j, m j x = y j a := by
    intro a
    by_cases ha : a ∈ S
    · obtain ⟨x, hx, e⟩ := key a ha
      exact ⟨x, fun _ => ⟨hx, fun j => congrFun e j⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose x hx using h1
  refine ⟨x, fun a ha => ⟨(hx a ha).1, fun g => ?_⟩, ?_⟩
  · rw [← sub_eq_zero]
    refine hinj _ fun j => ?_
    rw [map_sub, hm, map_smul, (hx a ha).2, hy j a ha, sub_self]
  · rw [← sub_eq_zero]
    refine hinj _ fun j => ?_
    rw [map_sub, map_sum, ← hs j, sub_eq_zero]
    exact Finset.sum_congr rfl fun a ha => (hx a ha).2 j

theorem subIner_rTensor_inj {Qp LL B V U : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [AddCommGroup B] [Module Qp B]
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    {n : ℕ} (p : Fin n → V →ₗ[LL] U) (hp : ∀ v, (∀ j, p j v = 0) → v = 0) (x : V ⊗[Qp] B)
    (hx : ∀ j, AlgebraTensorModule.rTensor Qp B (p j) x = 0) : x = 0 := by
  obtain ⟨q, hq⟩ := (LinearMap.pi p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot'.2 fun v hv => hp v fun j => congrFun hv j)
  have h1 : ∀ v, ∑ j, q (Pi.single j (p j v)) = v := by
    intro v
    rw [← map_sum, Finset.univ_sum_single]
    exact LinearMap.congr_fun hq v
  have h2 : ∀ z : V ⊗[Qp] B, ∑ j, AlgebraTensorModule.rTensor Qp B
      (q.comp (LinearMap.single LL (fun _ => U) j)) (AlgebraTensorModule.rTensor Qp B (p j) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      conv_rhs => rw [← h1 v, TensorProduct.sum_tmul]
      simp
    | add z w hz hw => simp only [map_add, Finset.sum_add_distrib, hz, hw]
  rw [← h2 x]
  simp [hx]

section General

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
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]

theorem subIner_mem_Dpcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ h ∈ PC.H, actVB PC.PD ρ h x = x := by
  have h1 : ∀ (h : PC.H) (z : V ⊗[Qp] B), actVB PC.PD' (PC.resH ρ) h z = actVB PC.PD ρ h z := by
    intro h z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
    | add z w hz hw => simp only [map_add, hz, hw]
  simp [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, sub_eq_zero, h1]

theorem subIner_actVB_mul (ρ : Representation LL G V) (g h : G) (z : V ⊗[Qp] B) :
    actVB PC.PD ρ g (actVB PC.PD ρ h z) = actVB PC.PD ρ (g * h) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem subIner_Dpcris_stable (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B)
    (hx : x ∈ PC.Dpcris ρ) : actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [subIner_mem_Dpcris] at hx ⊢
  intro h hh
  have h1 := hx (g⁻¹ * h * g⁻¹⁻¹) (PC.normal.conj_mem h hh g⁻¹)
  conv_rhs => rw [← h1]
  rw [subIner_actVB_mul, subIner_actVB_mul]
  congr 2
  group

theorem subIner_rTensor_actVB (ρ : Representation LL G V) (σ : Representation LL G U)
    (f : V →ₗ[LL] U) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (z : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f (actVB PC.PD ρ g z) =
      actVB PC.PD σ g (AlgebraTensorModule.rTensor Qp B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem subIner_mem_Eig (ρ : Representation LL G V) (I : Subgroup G) (a : I →* LLˣ) (x : V ⊗[Qp] B) :
    x ∈ PC.Eig ρ I a ↔ x ∈ PC.Dpcris ρ ∧ ∀ g : I, actVB PC.PD ρ g x = ((a g : LLˣ) : LL) • x := by
  simp [PotCrysData.Eig, Submodule.mem_iInf, sub_eq_zero]

theorem subIner_Dpcris_eq (ρ : Representation LL G V) {n : ℕ} (σ : Fin n → Representation LL G U)
    (p : Fin n → V →ₗ[LL] U) (hp : ∀ j g v, p j (ρ g v) = σ j g (p j v))
    (hinj : ∀ v, (∀ j, p j v = 0) → v = 0) (I : Subgroup G) (Sig : Finset (I →* LLˣ))
    (hσ : ∀ j, PC.Dpcris (σ j) = ⨆ a ∈ Sig, PC.Eig (σ j) I a) :
    PC.Dpcris ρ = ⨆ a ∈ Sig, PC.Eig ρ I a := by
  refine le_antisymm (fun d hd => ?_) (iSup₂_le fun a _ => inf_le_left)
  have h1 : ∀ j, ∃ μ : ∀ a, PC.Eig (σ j) I a,
      ∑ a ∈ Sig, (μ a : U ⊗[Qp] B) = AlgebraTensorModule.rTensor Qp B (p j) d := by
    intro j
    rw [← Submodule.mem_iSup_finset_iff_exists_sum, ← hσ j, subIner_mem_Dpcris]
    intro h hh
    rw [← subIner_rTensor_actVB PC ρ (σ j) (p j) (hp j), (subIner_mem_Dpcris PC ρ d).1 hd h hh]
  choose μ hμ using h1
  obtain ⟨x, hx, rfl⟩ := subIner_pullback (fun g : I => actVB PC.PD ρ g)
    (fun j (g : I) => actVB PC.PD (σ j) g) (fun j => AlgebraTensorModule.rTensor Qp B (p j))
    (fun j g z => subIner_rTensor_actVB PC ρ (σ j) (p j) (hp j) g z)
    (subIner_rTensor_inj p hinj) (fun (a : I →* LLˣ) g => ((a g : LLˣ) : LL))
    (fun a b hab => MonoidHom.ext fun g => Units.ext (congrFun hab g)) (PC.Dpcris ρ)
    (fun g z hz => subIner_Dpcris_stable PC ρ g z hz) Sig d hd (fun j a => μ j a)
    (fun j a _ g => ((subIner_mem_Eig PC (σ j) I a _).1 (μ j a).2).2 g) hμ
  refine Submodule.sum_mem _ fun a ha => ?_
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
    ((subIner_mem_Eig PC ρ I a _).2 (hx a ha)))

end General

theorem inertiaThrough_of_isSubFam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (ι : Type) (k : ℕ) (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsSubFam Ms W → ∀ (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p) → (∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig) → (pc P h hN hF hS).InertiaThrough W.ρ Sig := by
  intro l _ P K K' LL h hN hF hS ι k Ms W hW Sig h1 h2 h3
  obtain ⟨a, x, p, hp, hinj⟩ := hW
  refine ⟨h1, h2, ?_⟩
  exact subIner_Dpcris_eq (pc P h hN hF hS) W.ρ (fun j => matRep (Ms (x j))) p
    (fun j g v => by rw [hp]; simp [matRep]) hinj _ Sig fun j => (h3 (x j)).2.2

end GlobalTheory

end
