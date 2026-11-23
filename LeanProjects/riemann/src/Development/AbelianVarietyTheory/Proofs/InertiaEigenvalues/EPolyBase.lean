import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalApplyComm

noncomputable section
namespace GlobalTheory.BaseLatticeE
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

omit [TopologicalSpace G] [Algebra Qp LL] [TopologicalSpace LL] in

theorem exists_c (hk : (PD.p : k) = 0) (u : Oˣ) (hu : (u : O) = 1 + (PD.p : O)) :
    ∃ c : ℤ → O, WachUse.IsC PD LL c ∧ ∀ a, algebraMap O k (c a) = -(a : k) := by
  have hU : algebraMap O LL (u : O) = 1 + (PD.p : LL) := by rw [hu]; simp
  have hne : (1 + (PD.p : LL)) ≠ 0 := by rw [← hU]; exact (u.isUnit.map _).ne_zero
  have hinv : algebraMap O LL ((u⁻¹ : Oˣ) : O) = (1 + (PD.p : LL))⁻¹ := by
    rw [← hU]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]; simp
  have hk1 : algebraMap O k (u : O) = 1 := by rw [hu]; simp [hk]
  have hk2 : algebraMap O k ((u⁻¹ : Oˣ) : O) = 1 := by
    have : algebraMap O k ((u⁻¹ : Oˣ) : O) * algebraMap O k (u : O) = 1 := by rw [← map_mul]; simp
    rwa [hk1, mul_one] at this
  have key : ∀ a : ℤ, ∃ x : O, (PD.p : LL) * algebraMap O LL x = 1 - (1 + (PD.p : LL)) ^ a ∧
      algebraMap O k x = -(a : k) := by
    intro a
    induction a using Int.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ m ih =>
      obtain ⟨x, hx, hx'⟩ := ih
      refine ⟨x * (u : O) - 1, ?_, ?_⟩
      · rw [zpow_add_one₀ hne, map_sub, map_mul, hU, map_one]
        linear_combination (1 + (PD.p : LL)) * hx
      · rw [map_sub, map_mul, hk1, hx', map_one]; push_cast; ring
    | pred m ih =>
      obtain ⟨x, hx, hx'⟩ := ih
      refine ⟨(x + 1) * ((u⁻¹ : Oˣ) : O), ?_, ?_⟩
      · rw [zpow_sub_one₀ hne, map_mul, hinv, map_add, map_one]
        have h1 : (1 + (PD.p : LL)) * (1 + (PD.p : LL))⁻¹ = 1 := mul_inv_cancel₀ hne
        linear_combination (1 + (PD.p : LL))⁻¹ * hx + h1
      · rw [map_mul, map_add, hk2, hx', map_one]; push_cast; ring
  choose c hc hc' using key
  exact ⟨c, hc, hc'⟩

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n₀) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]; rfl

theorem sum_Del {M : Type} [AddCommMonoid M] (f : W.Gam → M) {δ : W.Gam} (hδ : δ ∈ W.DelF) :
    ∑ ε ∈ W.DelF, f (δ * ε) = ∑ ε ∈ W.DelF, f ε := by
  have hm : ∀ g, g ∈ W.DelF ↔ IsOfFinOrder g := fun g => by
    rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]
  refine Finset.sum_bij' (fun ε _ => δ * ε) (fun ε _ => δ⁻¹ * ε) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact (hm _).2 (((hm _).1 hδ).mul ((hm _).1 ha))
  · intro a ha; exact (hm _).2 (((hm _).1 hδ).inv.mul ((hm _).1 ha))
  · intro a _; simp
  · intro a _; simp
  · intro a _; rfl

theorem γA_q {δ : W.Gam} (hδ : δ ∈ W.DelF) :
    W.γA δ (W.π₀ + (PD.p : LetA O n₀)) = W.π₀ + (PD.p : LetA O n₀) := by
  rw [map_add, map_natCast]
  congr 1
  funext i
  change W.γ₀ δ W.π₀₁ = W.π₀₁
  rw [LocWach.π₀₁, map_add, map_sub, map_one, map_natCast, map_sum,
    ← sum_Del W (fun ε => W.γ₀ ε (1 + PowerSeries.X)) hδ]
  simp only [map_mul, AlgHom.mul_apply]

theorem γA_e (g : W.Gam) (i : ZMod n₀) : W.γA g (letE i) = letE i := by
  funext j
  change W.γ₀ g ((letE i : LetA O n₀) j) = (letE i : LetA O n₀) j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem card_Del {l : ℕ} (hl : 2 ≤ l) (hk : (PD.p : k) = 0) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩)
    (h1 : ∃ u : (k⟦X⟧)ˣ, ι (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l - 1))
    (h2 : ι (vv k) = ((PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) : k⸨X⸩)) :
    (W.DelF.card : k) = -1 := by
  obtain ⟨u, hu⟩ := h1
  have h3 : (PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) = (u : k⟦X⟧) * (PowerSeries.X : k⟦X⟧) ^ (l - 1) := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_mul, map_pow]
    rw [h2, vv_eq_coe_X] at hu
    exact hu
  have h4 := congrArg (PowerSeries.constantCoeff (R := k)) h3
  have h5 : PowerSeries.constantCoeff W.π₀₁ = 1 - (PD.p : O) + W.DelF.card := by
    rw [LocWach.π₀₁, map_add, map_sub, map_one, map_natCast, map_sum]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => (1 : O))]
    · simp
    · intro δ _
      rw [map_add, map_one, map_add, (W.γ₀_X δ).1]; simp
  have h6 : l - 1 ≠ 0 := by omega
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, h5] at h4
  simp [h6, hk] at h4
  linear_combination h4

theorem aeval_red {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V] (J : M →+ V)
    (hs : ∀ (c : O) y, J (c • y) = algebraMap O k c • J y) (ν : Module.End O M) (μ : Module.End k V)
    (hν : ∀ y, J (ν y) = μ (J y)) (f : Polynomial O) (y : M) :
    J (Polynomial.aeval ν f y) = Polynomial.aeval μ (f.map (algebraMap O k)) (J y) := by
  first
  | exact @_root_.GlobalTheory.AevalCommute.main
  | exact _root_.GlobalTheory.AevalCommute.main
  | (apply _root_.GlobalTheory.AevalCommute.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalCommute.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalCommute.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalCommute.main ..)

variable {W} {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀}
  {γ : W.Gam} (p : Pres W F ι τ γ) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
  (i : ZMod n)

def red : ↥(W.NΔ T) →+ Vc k A.m where
  toFun y := p.j T A q i ⟨y, y.2.2⟩
  map_zero' := map_zero (p.j T A q i)
  map_add' a b := map_add (p.j T A q i) ⟨a, a.2.2⟩ ⟨b, b.2.2⟩

variable {T A q}

theorem red_smul (hq : Onto T A q) (c : O) (y : ↥(W.NΔ T)) :
    red p T A q i (c • y) = algebraMap O k c • red p T A q i y := by
  have := p.j_smul T A q hq i (algebraMap O (LetA O n₀) c) (algebraMap k k⟦X⟧ (algebraMap O k c))
    ⟨y, y.2.2⟩ ⟨(c • y : ↥(W.NΔ T)), (c • y).2.2⟩ ?_ (by rw [algebraMap_smul]; rfl)
  · rw [algebraMap_smul] at this; exact this
  · have h1 : PowerSeries.map (algebraMap O k) (algebraMap O (LetA O n₀) c (τ i)) =
        algebraMap k k⟦X⟧ (algebraMap O k c) := by
      simp [PowerSeries.algebraMap_apply]
    rw [h1]
    exact ι.commutes _

theorem X_smul_eq (m : ℕ) (x : Vc k A.m) : (PowerSeries.X ^ m : k⟦X⟧) • x = vv k ^ (m : ℤ) • x := by
  rw [← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ m : k⟦X⟧) x, zpow_natCast, map_pow, vv_eq_coe_X]
  rfl

theorem red_ν (hq : Onto T A q) (ν : Module.End O ↥(W.NΔ T))
    (hν : ∀ y : ↥(W.NΔ T), W.γD T γ y - y = W.π₀ • ((ν y : ↥(W.NΔ T)) : W.DD T)) (y : ↥(W.NΔ T)) :
    red p T A q i (ν y) = nab ((F.D A).γ i) (red p T A q i y) := by
  have hg : W.γD T γ y ∈ DΔ W T := fun δ hδ => by
    rw [← W.γD_mul, mul_comm, W.γD_mul, y.2.2 δ hδ]
  have h1 := p.j_γ T A q hq i ⟨y, y.2.2⟩ ⟨_, hg⟩ rfl
  have h2 := p.j_smul T A q hq i W.π₀ PowerSeries.X ⟨(ν y : ↥(W.NΔ T)), (ν y).2.2⟩
    (⟨_, hg⟩ - ⟨y, y.2.2⟩) (by rw [← vv_eq_coe_X, p.ι_v]; rfl) (hν y)
  rw [map_sub, h1] at h2
  have h3 := X_smul_eq (A := A) 1 (red p T A q i (ν y))
  rw [pow_one, Nat.cast_one, zpow_one] at h3
  rw [nab_apply_eq]
  change _ = (vv k)⁻¹ • (((F.D A).γ i) (p.j T A q i ⟨y, y.2.2⟩) - p.j T A q i ⟨y, y.2.2⟩)
  rw [h2]
  change _ = (vv k)⁻¹ • ((PowerSeries.X : k⟦X⟧) • red p T A q i (ν y))
  rw [h3, smul_smul, inv_mul_cancel₀ (vv_ne_zero k), one_smul]

theorem red_div (hq : Onto T A q) (hk : (PD.p : k) = 0) (hc : (W.DelF.card : k) = -1) (s : ℕ)
    (y : ↥(W.NΔ T)) (z : W.DD T) (hz : z ∈ W.N T)
    (h : (letE (τ i) : LetA O n₀) • (y : W.DD T) = (W.π₀ + (PD.p : LetA O n₀)) ^ s • z) :
    ∃ z' : ↥(W.NΔ T), red p T A q i y = vv k ^ (s : ℤ) • red p T A q i z' := by
  have hz' : ∑ δ ∈ W.DelF, W.γD T δ z ∈ W.NΔ T := by
    refine ⟨Submodule.sum_mem _ fun δ _ => W.N_Γ T δ z hz, fun δ hδ => ?_⟩
    rw [map_sum, ← sum_Del W (fun ε => W.γD T ε z) hδ]
    simp only [W.γD_mul]
  have he : (letE (τ i) : LetA O n₀) • (y : W.DD T) ∈ DΔ W T := fun δ hδ => by
    rw [γD_smulA, γA_e, y.2.2 δ hδ]
  have h1 := p.j_smul T A q hq i (letE (τ i)) 1 ⟨y, y.2.2⟩ ⟨_, he⟩ (by simp [letE]) rfl
  have h2 : W.DelF.card • ((letE (τ i) : LetA O n₀) • (y : W.DD T)) =
      (W.π₀ + (PD.p : LetA O n₀)) ^ s • ∑ δ ∈ W.DelF, W.γD T δ z := by
    rw [Finset.smul_sum, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [← he δ hδ, h, γD_smulA, map_pow, γA_q W hδ]
  have h3 := p.j_smul T A q hq i ((W.π₀ + (PD.p : LetA O n₀)) ^ s) (PowerSeries.X ^ s) ⟨_, hz'.2⟩
    (W.DelF.card • ⟨_, he⟩) ?_ h2
  · rw [map_nsmul, h1, one_smul, ← Nat.cast_smul_eq_nsmul k, hc, neg_one_smul, X_smul_eq] at h3
    refine ⟨-⟨_, hz'⟩, ?_⟩
    rw [map_neg, smul_neg]
    exact (neg_eq_iff_eq_neg.1 h3)
  · have h4 : PowerSeries.map (algebraMap O k) (((W.π₀ + (PD.p : LetA O n₀)) ^ s) (τ i)) =
        PowerSeries.map (algebraMap O k) W.π₀₁ ^ s := by
      have h5 : ((PD.p : ℕ) : k⟦X⟧) = 0 := by
        rw [← map_natCast (algebraMap k k⟦X⟧), hk, map_zero]
      rw [Pi.pow_apply, Pi.add_apply, Pi.natCast_apply, map_pow, map_add, map_natCast, h5, add_zero]
      rfl
    rw [h4, map_pow, map_pow, map_pow, ← p.ι_v, vv_eq_coe_X]

theorem ePoly_gen [CharP k l] (hp : PD.p = l) (hl : 2 ≤ l) (hq : Onto T A q)
    (h1 : ∃ u : (k⟦X⟧)ˣ, ι (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l - 1))
    (hγ : (W.χΓ γ : O) = 1 + (PD.p : O)) (hS : WachUse.SenOp W) (U : ZMod n₀ → Multiset ℤ)
    (hU : CrysWith PD W.emb T.ρ U) (N : Submodule k⟦X⟧ (Vc k A.m))
    (hN : ∀ y, y ∈ N ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (s : ℕ)
    (hs : ∀ u ∈ U (τ i), ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) :
    EPoly ((F.D A).γ i) N s := by
  classical
  have hk : (PD.p : k) = 0 := by rw [hp]; exact CharP.cast_eq_zero k l
  have hc := card_Del W hl hk ι h1 p.ι_v
  obtain ⟨c, hc1, hc2⟩ := exists_c (PD := PD) (LL := LL) hk (W.χΓ γ) hγ
  obtain ⟨ν, hν, hmid, -⟩ := hS T U hU γ hγ c hc1
  set I := ((Finset.range s) ×ˢ (U (τ i)).toFinset).image (fun p => (p.1 : ℤ) - p.2) with hI
  have key : ∀ y : ↥(W.NΔ T), Polynomial.aeval (nab ((F.D A).γ i))
      (∏ m ∈ I, (Polynomial.X + Polynomial.C (m : k))) (red p T A q i y) ∈ sh s N := by
    intro y
    obtain ⟨z, hz, h⟩ := hmid (τ i) s y
    obtain ⟨z', hz'⟩ := red_div p i hq hk hc s _ z hz h
    rw [aeval_red (red p T A q i) (red_smul p i hq) ν _ (red_ν p i hq ν hν), Polynomial.map_prod] at hz'
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc2, map_neg, sub_neg_eq_add] at hz'
    exact mem_sh_iff_exists.2 ⟨_, (hN _).2 ⟨⟨z', z'.2.2⟩, z'.2.1, rfl⟩, hz'.symm⟩
  refine ⟨∏ m ∈ I.erase 0, (Polynomial.X + Polynomial.C (m : k)), ?_, fun x hx => ?_⟩
  · rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro m hm h0
    obtain ⟨hm0, hm⟩ := Finset.mem_erase.1 hm
    obtain ⟨⟨a, u⟩, hau, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨ha, hu⟩ := Finset.mem_product.1 hau
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add, CharP.intCast_eq_zero_iff k l] at h0
    exact hm0 (sub_eq_zero.2 (hs u (Multiset.mem_toFinset.1 hu) a (Finset.mem_range.1 ha) h0))
  · obtain ⟨x, hx1, rfl⟩ := (hN x).1 hx
    let y : ↥(W.NΔ T) := ⟨x, hx1, x.2⟩
    have hy : p.j T A q i x = red p T A q i y := rfl
    rw [hy]
    by_cases h0 : (0 : ℤ) ∈ I
    · have := key y
      rw [← Finset.mul_prod_erase I _ h0, map_mul, Module.End.mul_apply] at this
      simpa using this
    · have := key (ν y)
      rw [red_ν p i hq ν hν] at this
      rw [Finset.erase_eq_of_notMem h0]
      have h2 : ∀ (f : Polynomial k) (μ : Module.End k (Vc k A.m)) w,
          μ (Polynomial.aeval μ f w) = Polynomial.aeval μ f (μ w) := fun f μ w => by
        have := congrArg (fun g => Polynomial.aeval μ g w) (mul_comm Polynomial.X f)
        simpa using this
      rw [h2]; exact this

end Gen

theorem ePoly_base : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ (i : ZMod S.n) (s : ℕ), (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s := by
  intro l _ P H S k _ _ _ _ R ι F τ γ p hι hτ hγ hQ T A q U hq _ hU N hN i s hs
  have hb : Function.Bijective S.emb := S.hyp.1.2.2.2.1
  have hl : 5 ≤ l := S.hyp.1.1
  let e := Equiv.ofBijective _ hb
  have hp : (P.PD S.K).p = l := P.PD_p S.K
  refine ePoly_gen p i hp (by omega) hq hι.1 (by rw [hp]; exact hγ) hQ.2.2.2.2.2
    (fun j => U (e.symm ((S.W H).emb j))) ⟨hU.1, fun j => ?_⟩ (N i) (hN i) s ?_
  · have := hU.2 (e.symm ((S.W H).emb j))
    have h2 : S.emb (e.symm ((S.W H).emb j)) = (S.W H).emb j := e.apply_symm_apply _
    rwa [h2] at this
  · have h2 : e.symm ((S.W H).emb (τ i)) = i := by rw [hτ]; exact e.symm_apply_apply i
    simpa only [h2] using hs

end GlobalTheory.BaseLatticeE
