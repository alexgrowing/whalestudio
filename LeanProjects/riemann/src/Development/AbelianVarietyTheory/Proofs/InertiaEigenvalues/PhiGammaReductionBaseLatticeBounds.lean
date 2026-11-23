import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReductionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantsReductionIsLatticeStatement

noncomputable section
namespace GlobalTheory.BaseABC
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

section Ser
variable {k : Type} [Field k]

theorem coe_inj {a b : k⟦X⟧} (h : (a : k⸨X⸩) = (b : k⸨X⸩)) : a = b :=
  HahnSeries.ofPowerSeries_injective (Γ := ℤ) h

theorem card_ne_zero (l : ℕ) [Fact l.Prime] [CharP k l] {α : Type} (s : Finset α)
    (e : {δ // δ ∈ s} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}) : ((s.card : ℕ) : k) ≠ 0 := by
  classical
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hpos : 0 < s.card := Finset.card_pos.2 ⟨(e.symm ⟨1, one_pow _⟩).1, (e.symm ⟨1, one_pow _⟩).2⟩
  have hle : s.card ≤ l - 1 := by
    have h1 : s.attach.card ≤ (Polynomial.nthRoots (l - 1) (1 : ℤ_[l])).toFinset.card := by
      refine Finset.card_le_card_of_injOn (fun δ => (e δ).1) (fun δ _ => ?_) (fun a _ b _ h => ?_)
      · simp only [Finset.mem_coe, Multiset.mem_toFinset]
        exact (Polynomial.mem_nthRoots (by omega)).2 (e δ).2
      · exact e.injective (Subtype.ext h)
    rw [Finset.card_attach] at h1
    exact h1.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _))
  intro h
  have := Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff k l _).1 h)
  omega

theorem X_dvd_of {l : ℕ} [Fact l.Prime] [CharP k l] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩}
    (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (c b : k⟦X⟧) (h : ι (c : k⸨X⸩) = (b : k⸨X⸩))
    (hb : PowerSeries.constantCoeff b = 0) : ∃ c' : k⟦X⟧, c = PowerSeries.X * c' := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨⟨u, hu⟩, h2, -⟩ := hι
  set s : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) c
  obtain ⟨t, ht⟩ := h2 s
  have ha : (c : k⸨X⸩) = vv k * (s : k⸨X⸩) + algebraMap k k⸨X⸩ (PowerSeries.constantCoeff c) := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const c, map_add, map_mul, ← vv_eq_coe_X]
    rfl
  have hb' : b = (u : k⟦X⟧) * PowerSeries.X ^ (l - 1) * t + PowerSeries.C (PowerSeries.constantCoeff c) := by
    apply coe_inj
    rw [← h, ha, map_add ι, map_mul ι, AlgHom.commutes, hu, ht, vv_eq_coe_X, map_add, map_mul, map_mul, map_pow]
    rfl
  have h0 : PowerSeries.constantCoeff c = 0 := by
    rw [hb'] at hb
    simpa [show l - 1 ≠ 0 by omega] using hb
  exact PowerSeries.X_dvd_iff.2 h0

theorem coe_smul' {m : ℕ} (c : k⟦X⟧) (y : Vc k m) : c • y = (c : k⸨X⸩) • y :=
  (algebraMap_smul k⸨X⸩ c y).symm

end Ser

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀)

theorem sum_shift {M : Type} [AddCommMonoid M] (f : W.Gam → M) {δ : W.Gam} (hδ : δ ∈ W.DelF) :
    ∑ g ∈ W.DelF, f (δ * g) = ∑ g ∈ W.DelF, f g := by
  have key : ∀ g, g ∈ W.DelF ↔ IsOfFinOrder g := fun g => by rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]
  refine Finset.sum_nbij' (fun g => δ * g) (fun g => δ⁻¹ * g) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    exact (key _).2 (((key _).1 hδ).mul ((key _).1 hg))
  · intro g hg
    exact (key _).2 (((key _).1 hδ).inv.mul ((key _).1 hg))
  · intro g _; simp
  · intro g _; simp
  · intro g _; rfl

def tr₀ (b : O⟦X⟧) : O⟦X⟧ := ∑ δ ∈ W.DelF, W.γ₀ δ b

def trA (a : LetA O n₀) : LetA O n₀ := fun t => tr₀ W (a t)

def trD (T : LocLat G Qp LL O) : W.DD T →+ ↥(DΔ W T) :=
  AddMonoidHom.codRestrict (∑ δ ∈ W.DelF, W.γD T δ).toAddMonoidHom (DΔ W T) (fun z δ hδ => by
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.sum_apply, map_sum, ← W.γD_mul]
    exact sum_shift W (fun g => W.γD T g z) hδ)

theorem trD_coe (T : LocLat G Qp LL O) (z : W.DD T) : (trD W T z : W.DD T) = ∑ δ ∈ W.DelF, W.γD T δ z := by
  exact LinearMap.sum_apply _ _ _

theorem tr₀_inv (b : O⟦X⟧) {δ : W.Gam} (hδ : δ ∈ W.DelF) : W.γ₀ δ (tr₀ W b) = tr₀ W b := by
  simp only [tr₀, map_sum, ← AlgHom.mul_apply, ← map_mul]
  exact sum_shift W (fun g => W.γ₀ g b) hδ

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n₀) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n₀) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n₀) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n₀) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem trD_smul (T : LocLat G Qp LL O) (a : LetA O n₀) (x : ↥(DΔ W T)) :
    (trD W T (a • (x : W.DD T)) : W.DD T) = trA W a • (x : W.DD T) := by
  have h : trA W a = ∑ δ ∈ W.DelF, W.γA δ a := by
    funext t
    rw [Finset.sum_apply]
    rfl
  rw [trD_coe, h, Finset.sum_smul]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  rw [γD_smulA, x.2 δ hδ]

theorem trD_mem (T : LocLat G Qp LL O) {z : W.DD T} (hz : z ∈ W.N T) : (trD W T z : W.DD T) ∈ W.N T := by
  rw [trD_coe]
  exact Submodule.sum_mem _ fun δ _ => W.N_Γ T δ z hz

theorem span_ind {A D V : Type} [CommRing A] [AddCommGroup D] [Module A D] [AddCommGroup V] (J : D →+ V)
    (M : AddSubgroup V) (S : Set D) (g : A) (hS : ∀ s ∈ S, ∀ a : A, J ((g * a) • s) ∈ M) {z : D}
    (hz : z ∈ Submodule.span A S) : J (g • z) ∈ M := by
  have : ∀ a : A, J ((g * a) • z) ∈ M := by
    induction hz using Submodule.span_induction with
    | mem s hs => exact hS s hs
    | zero => intro a; simp
    | add x y _ _ hx hy => intro a; rw [smul_add, map_add]; exact M.add_mem (hx a) (hy a)
    | smul r x _ hx => intro a; rw [smul_smul, mul_assoc]; exact hx _
  simpa using this 1

variable {k : Type} [Field k] [Algebra O k] {l : ℕ} [Fact l.Prime] [CharP k l] {n : ℕ} {R : RingPG k l}
  {ι : k⸨X⸩ →ₐ[k] k⸨X⸩}

variable (k l) in

def DelAct : Prop :=
  ∃ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a,
    PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 a) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) a)

variable {W}

theorem tr_exists (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (ha : DelAct W k l) (b : O⟦X⟧) :
    ∃ c : k⟦X⟧, ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (tr₀ W b) : k⟦X⟧) : k⸨X⸩) := by
  obtain ⟨e, he⟩ := ha
  refine (hι.2.2.1 _).1 fun z hz => ?_
  have := he (e.symm ⟨z, hz⟩) (tr₀ W b)
  rw [e.apply_symm_apply, tr₀_inv W b (e.symm ⟨z, hz⟩).2] at this
  exact this.symm

theorem tr_of (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (ha : DelAct W k l) (b : O⟦X⟧) (c : k⟦X⟧)
    (h : ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) b : k⟦X⟧) : k⸨X⸩)) :
    ι (((W.DelF.card : k⟦X⟧) * c : k⟦X⟧) : k⸨X⸩) =
      ((PowerSeries.map (algebraMap O k) (tr₀ W b) : k⟦X⟧) : k⸨X⸩) := by
  obtain ⟨e, he⟩ := ha
  have h1 := (hι.2.2.1 _).2 ⟨c, h⟩
  have h2 : PowerSeries.map (algebraMap O k) (tr₀ W b) =
      (W.DelF.card : k⟦X⟧) * PowerSeries.map (algebraMap O k) b := by
    rw [tr₀, map_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [he ⟨δ, hδ⟩, h1 _ (e ⟨δ, hδ⟩).2]
  rw [h2, map_mul, map_mul, map_mul, h, map_natCast, map_natCast]

theorem mem_of_card_smul (ha : DelAct W k l) {m : ℕ} (M : Submodule k⟦X⟧ (Vc k m)) (c : k⟦X⟧) (y : Vc k m)
    (h : ((W.DelF.card : k⟦X⟧) * c) • y ∈ M) : c • y ∈ M := by
  obtain ⟨e, -⟩ := ha
  have hd := card_ne_zero (k := k) l _ e
  have := M.smul_mem (PowerSeries.C ((W.DelF.card : k)⁻¹)) h
  rwa [smul_smul, ← mul_assoc, ← map_natCast (PowerSeries.C (R := k)), ← map_mul, inv_mul_cancel₀ hd, map_one,
    one_mul] at this

theorem exists_lift (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (hp : PD.p = l) (hs : W.s = 1)
    (hk : Function.Surjective (algebraMap O k)) :
    ∃ u : O⟦X⟧, ∀ (t : ZMod n₀) (w : ℕ), ι ((PowerSeries.X ^ w : k⟦X⟧) : k⸨X⸩) =
      ((PowerSeries.map (algebraMap O k) (((fun _ => u ^ w) * (W.Q ^ w * letE t) : LetA O n₀) t) : k⟦X⟧) :
        k⸨X⸩) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨u, hu⟩ := hι.1
  obtain ⟨u', hu'⟩ := PowerSeries.map_surjective (algebraMap O k) hk (u : k⟦X⟧)
  haveI : CharP k⟦X⟧ l := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective l
  have hq : PowerSeries.map (algebraMap O k) W.q₀ = PowerSeries.X ^ (l - 1) := by
    have := congrArg (PowerSeries.map (algebraMap O k)) W.q₀_def
    rw [hp, map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X, add_pow_char, one_pow,
      add_sub_cancel_left] at this
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := k))
    rw [this, ← pow_succ']
    congr 1; omega
  have hQ : W.Q = fun _ => W.q₀ := by
    simp only [LocWach.Q, hs, Nat.sub_self, pow_zero]
    rfl
  refine ⟨u', fun t w => ?_⟩
  simp only [hQ, Pi.mul_apply, Pi.pow_apply, letE, Pi.single_eq_same, mul_one, map_mul, map_pow, hu', hq]
  rw [← vv_eq_coe_X, hu, mul_pow]

variable {F : DFun R n G} {τ : ZMod n → ZMod n₀} {γ : W.Gam} (p : Pres W F ι τ γ)
  {T : LocLat G Qp LL O} {A : Ob k G} {q : ↥T.L.T →ₗ[O] (Fin A.m → k)}

theorem j_tr (hq : Onto T A q) (i : ZMod n) (a : LetA O n₀) (x : ↥(DΔ W T)) (c : k⟦X⟧)
    (h : ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (tr₀ W (a (τ i))) : k⟦X⟧) : k⸨X⸩)) :
    p.j T A q i (trD W T (a • (x : W.DD T))) = c • p.j T A q i x :=
  p.j_smul T A q hq i (trA W a) c x _ h (trD_smul W T a x)

def φΔ (x : ↥(DΔ W T)) : ↥(DΔ W T) :=
  ⟨W.φD T x, fun δ hδ => by rw [← W.φγ_comm, x.2 δ hδ]⟩

def γΔ (g : W.Gam) (x : ↥(DΔ W T)) : ↥(DΔ W T) :=
  ⟨W.γD T g x, fun δ hδ => by rw [← W.γD_mul, mul_comm, W.γD_mul, x.2 δ hδ]⟩

theorem X_pow_smul {m : ℕ} (w : ℕ) (y : Vc k m) : (PowerSeries.X ^ w : k⟦X⟧) • y = vv k ^ (w : ℤ) • y := by
  rw [coe_smul', zpow_natCast, vv_eq_coe_X, map_pow]

theorem condA (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (ha : DelAct W k l) (hp : PD.p = l) (hs : W.s = 1)
    (hk : Function.Surjective (algebraMap O k)) (hq : Onto T A q) (N : Lats k n A.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (i : ZMod n) (w : ℕ)
    (h : ∀ x ∈ W.N T, W.Q ^ w • (letE (τ i) : LetA O n₀) • W.φD T x ∈ W.N T) :
    pull ((F.D A).φ i) (N (i - 1)) ≤ sh (-(w : ℤ)) (N i) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, rfl⟩ := (hN _ _).1 hy
  obtain ⟨u, hu⟩ := exists_lift (W := W) hι hp hs hk
  rw [SetLike.mem_coe, mem_sh_iff_smul_mem, neg_neg, ← X_pow_smul, ← p.j_φ T A q hq i x (φΔ x) rfl]
  apply mem_of_card_smul ha
  rw [← j_tr p hq i _ _ _ (tr_of hι ha _ _ (hu (τ i) w))]
  refine (hN _ _).2 ⟨_, trD_mem W T ?_, rfl⟩
  rw [mul_smul, mul_smul]
  exact (W.N T).smul_mem _ (h x hx)

theorem condB (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (ha : DelAct W k l) (hp : PD.p = l) (hs : W.s = 1)
    (hk : Function.Surjective (algebraMap O k)) (hq : Onto T A q)
    (hb : W.N T ≤ Submodule.span (LetA O n₀) (W.NΔ T : Set (W.DD T))) (N : Lats k n A.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (i : ZMod n) (w : ℕ)
    (h : ∀ y ∈ W.N T, W.Q ^ w • (letE (τ i) : LetA O n₀) • y ∈ W.φpull T) :
    sh (w : ℤ) (N i) ≤ pull ((F.D A).φ i) (N (i - 1)) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 hz
  obtain ⟨x, hx, rfl⟩ := (hN _ _).1 hy
  obtain ⟨u, hu⟩ := exists_lift (W := W) hι hp hs hk
  rw [← X_pow_smul]
  apply mem_of_card_smul ha
  rw [← j_tr p hq i _ _ _ (tr_of hι ha _ _ (hu (τ i) w)), mul_smul, mul_smul]
  have hsp : W.φpull T ≤ Submodule.span (LetA O n₀) (W.φD T '' (W.NΔ T : Set (W.DD T))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    have hs' := hb hs
    clear hs
    induction hs' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [φD_smulA]; exact Submodule.smul_mem _ _ hb
  refine span_ind ((p.j T A q i).comp (trD W T)) (pull ((F.D A).φ i) (N (i - 1))).toAddSubgroup _ _ ?_
    (hsp (h x hx))
  rintro _ ⟨s, hs, rfl⟩ a
  obtain ⟨c, hc⟩ := tr_exists hι ha (((fun _ => u ^ w) * a : LetA O n₀) (τ i))
  have := j_tr p hq i _ (φΔ ⟨s, hs.2⟩) c hc
  change p.j T A q i (trD W T (_ • ((φΔ ⟨s, hs.2⟩ : ↥(DΔ W T)) : W.DD T))) ∈ pull _ _
  rw [this, p.j_φ T A q hq i ⟨s, hs.2⟩ _ rfl]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, (hN _ _).2 ⟨_, hs.1, rfl⟩, rfl⟩)

theorem condC (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (ha : DelAct W k l) (hq : Onto T A q)
    (hb : W.N T ≤ Submodule.span (LetA O n₀) (W.NΔ T : Set (W.DD T))) (N : Lats k n A.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (i : ZMod n) :
    CondC ((F.D A).γ i) (N i) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (hN _ _).1 hy
  obtain ⟨z, hz, hz'⟩ := W.N_π T γ x hx
  rw [← p.j_γ T A q hq i x (γΔ γ x) rfl, ← map_sub, ← one_smul k⟦X⟧ (p.j T A q i _)]
  apply mem_of_card_smul ha
  rw [← j_tr p hq i 1 _ _ (tr_of hι ha _ _ (by simp)), one_smul]
  have e1 : ((γΔ γ x - x : ↥(DΔ W T)) : W.DD T) = (letπ : LetA O n₀) • z := hz'
  rw [e1]
  refine span_ind ((p.j T A q i).comp (trD W T)) (sh 1 (N i)).toAddSubgroup _ _ ?_ (hb hz)
  intro s hs a
  obtain ⟨c, hc⟩ := tr_exists hι ha ((letπ * a : LetA O n₀) (τ i))
  have := j_tr p hq i _ ⟨s, hs.2⟩ c hc
  obtain ⟨c', rfl⟩ := X_dvd_of hι c _ hc (by
    have h0 : PowerSeries.constantCoeff (tr₀ W ((letπ * a : LetA O n₀) (τ i))) = 0 := by
      rw [tr₀, map_sum]
      refine Finset.sum_eq_zero fun δ _ => ?_
      rw [Pi.mul_apply, map_mul, map_mul, letπ, (W.γ₀_X δ).1, zero_mul]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero])
  change p.j T A q i (trD W T (_ • ((⟨s, hs.2⟩ : ↥(DΔ W T)) : W.DD T))) ∈ sh 1 _
  rw [this]
  refine mem_sh_iff_exists.2 ⟨c' • p.j T A q i ⟨s, hs.2⟩, (N i).smul_mem _ ((hN _ _).2 ⟨_, hs.1, rfl⟩), ?_⟩
  rw [mul_smul, ← pow_one PowerSeries.X, X_pow_smul, Nat.cast_one]

theorem cond_all (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (ha : DelAct W k l) (hp : PD.p = l) (hs : W.s = 1)
    (hk : Function.Surjective (algebraMap O k)) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (he : Function.Bijective emb)
    (hτ : ∀ i, W.emb (τ i) = emb i) (hQN : GlobalTheory.WachUse.QN W) (hq : Onto T A q) (U : ZMod n → Multiset ℤ)
    (hU : CrysWith PD emb T.ρ U) (N : Lats k n A.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (w w' : ZMod n → ℕ)
    (hw : ∀ i, ∀ u ∈ U i, -(w i : ℤ) ≤ u ∧ u ≤ w' i) :
    CondAB (F.D A).φ (fun i => w i) (fun i => w' i) N ∧ ∀ i, CondC ((F.D A).γ i) (N i) := by
  obtain ⟨b, hb1, -, hb2⟩ := hQN.1 T hU.1
  have hb : W.N T ≤ Submodule.span (LetA O n₀) (W.NΔ T : Set (W.DD T)) := by
    rw [hb2]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact hb1 j
  choose σ hσ using fun t => he.2 (W.emb t)
  have hστ : ∀ i, σ (τ i) = i := fun i => he.1 ((hσ _).trans (hτ i))
  have hH := hQN.2.1 T (fun t => U (σ t)) (fun t => w (σ t)) (fun t => w' (σ t))
    ⟨hU.1, fun t => by rw [← hσ]; exact hU.2 _⟩ (fun t => hw _)
  refine ⟨fun i => ?_, condC p hι ha hq hb N hN⟩
  have h := hH (τ i)
  simp only [hστ] at h
  exact ⟨condA p hι ha hp hs hk hq N hN i _ h.1, condB p hι ha hp hs hk hq hb N hN i _ h.2⟩

end Gen

theorem base_abc : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ w w' : ZMod S.n → ℕ, (∀ i, ∀ u ∈ U i, -(w i : ℤ) ≤ u ∧ u ≤ w' i) → ABC (F.D A) (fun i => w i) (fun i => w' i) N := by
  intro l _ P H S k _ _ _ hk R ι F τ γ p hι hτ hγ hQN T A q U hq hker hU N hN w w' hw
  obtain ⟨N', hN', hL⟩ := GlobalTheory.T.wachDeltaInvariants_reduction_isLattice H S k hk ι F τ γ p hι hτ hγ hQN T A q U hq hker hU
  have hNN : N = N' := funext fun i => Submodule.ext fun y => (hN i y).trans (hN' i y).symm
  subst hNN
  exact ⟨hL, cond_all p hι (GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller H S k).2 (P.PD_p S.K) (H.W_s _ _ _ _) hk.1 S.emb S.hyp.1.2.2.2.1 hτ hQN
    hq U hU N hN w w' hw⟩

end GlobalTheory.BaseABC
