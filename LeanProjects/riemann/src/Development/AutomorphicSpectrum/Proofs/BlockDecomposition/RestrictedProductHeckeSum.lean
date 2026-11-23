import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSumFiberDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictedProductQuotientStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.FinActSum

variable {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)]

def fac (V : ∀ i, Subgroup (Hl i)) (f : ∀ i, Hl i → ℂ) (T : List ι) (j : ι) (h : Hl j) : ℂ :=
  if j ∈ T then f j h else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) h

def prodF (p : ∀ i, Γ →* Hl i) (V : ∀ i, Subgroup (Hl i)) (f : ∀ i, Hl i → ℂ) (T : List ι) (x : Γ) : ℂ :=
  ∏ᶠ j, fac V f T j (p j x)

def comp (e : ∀ i, Hl i →* Γ) (KH : ∀ i, Subgroup (Hl i)) (f : ∀ i, Hl i → ℂ) (g : Γ → ℂ) (T : List ι) : Γ → ℂ :=
  T.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g

theorem fac_mul {V : ∀ i, Subgroup (Hl i)} {f : ∀ i, Hl i → ℂ}
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x) (T : List ι) (j : ι) (h v : Hl j) (hv : v ∈ V j) :
    fac V f T j (h * v) = fac V f T j h := by
  unfold fac
  split_ifs with hj
  · exact hfV j v hv h
  · simp only [Set.indicator_apply, SetLike.mem_coe, Subgroup.mul_mem_cancel_right _ hv, Pi.one_apply]

theorem fac_finite {p : ∀ i, Γ →* Hl i} {V : ∀ i, Subgroup (Hl i)} (f : ∀ i, Hl i → ℂ)
    (hS : ∀ x, ∀ᶠ j in cofinite, p j x ∈ V j) (T : List ι) (x : Γ) :
    (Function.mulSupport fun j => fac V f T j (p j x)).Finite := by
  refine ((Filter.eventually_cofinite.1 (hS x)).union (List.finite_toSet T)).subset ?_
  intro j hj
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  apply hj
  have hjT : j ∉ T := hc.2
  simp [fac, hjT, hc.1]

theorem prodF_mul {p : ∀ i, Γ →* Hl i} {V : ∀ i, Subgroup (Hl i)} {f : ∀ i, Hl i → ℂ}
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x) (T : List ι) (x u : Γ) (hu : ∀ j, p j u ∈ V j) :
    prodF p V f T (x * u) = prodF p V f T x := by
  unfold prodF
  refine finprod_congr fun j => ?_
  rw [map_mul, fac_mul hfV T j _ _ (hu j)]

theorem fac_ne_zero {p : ∀ i, Γ →* Hl i} {V : ∀ i, Subgroup (Hl i)} {f : ∀ i, Hl i → ℂ}
    (hS : ∀ x, ∀ᶠ j in cofinite, p j x ∈ V j) (T : List ι) (x : Γ) (h : prodF p V f T x ≠ 0) (j : ι) :
    fac V f T j (p j x) ≠ 0 := fun h0 =>
  h (finprod_eq_zero _ j h0 (fac_finite f hS T x))

theorem prodF_split {p : ∀ i, Γ →* Hl i} {e : ∀ i, Hl i →* Γ} {V : ∀ i, Subgroup (Hl i)} {f : ∀ i, Hl i → ℂ}
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hS : ∀ x, ∀ᶠ j in cofinite, p j x ∈ V j) {i : ι} {T : List ι} (hi : i ∉ T) (m : Hl i) (q : Γ) :
    (V i : Set (Hl i)).indicator (1 : Hl i → ℂ) (p i q) * prodF p V f (i :: T) (e i m * q) =
      f i m * prodF p V f T q := by
  have h1 : prodF p V f (i :: T) (e i m * q) = fac V f (i :: T) i (p i (e i m * q)) *
      ∏ᶠ (j) (_ : j ≠ i), fac V f (i :: T) j (p j (e i m * q)) :=
    (mul_finprod_cond_ne i (fac_finite f hS (i :: T) (e i m * q))).symm
  have h2 : prodF p V f T q = fac V f T i (p i q) * ∏ᶠ (j) (_ : j ≠ i), fac V f T j (p j q) :=
    (mul_finprod_cond_ne i (fac_finite f hS T q)).symm
  have h3 : (∏ᶠ (j) (_ : j ≠ i), fac V f (i :: T) j (p j (e i m * q))) =
      ∏ᶠ (j) (_ : j ≠ i), fac V f T j (p j q) := by
    refine finprod_congr fun j => finprod_congr fun hj => ?_
    rw [map_mul, hpe' i j m (Ne.symm hj), one_mul]
    simp [fac, hj]
  have h4 : fac V f (i :: T) i (p i (e i m * q)) = f i (m * p i q) := by
    rw [map_mul, hpe]
    simp [fac]
  have h5 : fac V f T i (p i q) = (V i : Set (Hl i)).indicator (1 : Hl i → ℂ) (p i q) := by
    simp [fac, hi]
  rw [h1, h2, h3, h4, h5]
  by_cases hq : p i q ∈ V i
  · have : (V i : Set (Hl i)).indicator (1 : Hl i → ℂ) (p i q) = 1 := by simp [hq]
    rw [this, hfV i _ hq m]
    ring
  · have : (V i : Set (Hl i)).indicator (1 : Hl i → ℂ) (p i q) = 0 := by simp [hq]
    rw [this]
    ring

theorem e_comm {p : ∀ i, Γ →* Hl i} {e : ∀ i, Hl i →* Γ}
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y) {i j : ι} (hij : i ≠ j) (v : Hl i) (m : Hl j) :
    e i v * e j m = e j m * e i v := by
  refine hsep _ _ fun k => ?_
  rw [map_mul, map_mul]
  by_cases hki : i = k
  · subst hki
    rw [hpe' j i m hij.symm, hpe, mul_one, one_mul]
  · rw [hpe' i k v hki, one_mul, mul_one]

theorem comp_inv {p : ∀ i, Γ →* Hl i} {e : ∀ i, Hl i →* Γ} {KH V : ∀ i, Subgroup (Hl i)} {f : ∀ i, Hl i → ℂ}
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y) {g : Γ → ℂ}
    (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x) {i : ι} {v : Hl i} (hv : v ∈ V i)
    (T : List ι) (hi : i ∉ T) (x : Γ) :
    comp e KH f g T (x * e i v) = comp e KH f g T x := by
  induction T generalizing x with
  | nil =>
    refine hg (e i v) (fun j => ?_) x
    by_cases hij : i = j
    · subst hij
      rw [hpe]
      exact hv
    · rw [hpe' i j v hij]
      exact one_mem _
  | cons j T ih =>
    have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
    have hiT : i ∉ T := fun h => hi (List.mem_cons_of_mem _ h)
    change hint (KH j) (fun m => f j m * comp e KH f g T (x * e i v * e j m)) =
      hint (KH j) (fun m => f j m * comp e KH f g T (x * e j m))
    congr 1
    funext m
    rw [mul_assoc x, e_comm hpe hpe' hsep hij, ← mul_assoc, ih hiT]

theorem coset_one {G : Type} [Group G] (L : Subgroup G) (q : G ⧸ L) :
    q = ((1 : G) : G ⧸ L) ↔ q.out ∈ L := by
  constructor
  · rintro rfl
    simpa using QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : G) : G ⧸ L)).symm
  · intro h
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using L.inv_mem h)

theorem sum_nil {p : ∀ i, Γ →* Hl i} {V : ∀ i, Subgroup (Hl i)} (f : ∀ i, Hl i → ℂ)
    {g : Γ → ℂ} (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x)
    (hS : ∀ x, ∀ᶠ j in cofinite, p j x ∈ V j) (y : Γ) :
    ∑ᶠ q : Γ ⧸ (⨅ i, (V i).comap (p i)), prodF p V f [] q.out * g (y * q.out) = g y := by
  have hmem : ∀ x : Γ, x ∈ (⨅ i, (V i).comap (p i)) ↔ ∀ j, p j x ∈ V j := by
    intro x
    simp [Subgroup.mem_iInf]
  rw [finsum_eq_single _ ((1 : Γ) : Γ ⧸ (⨅ i, (V i).comap (p i)))]
  · have ho := (coset_one _ _).1 (rfl : ((1 : Γ) : Γ ⧸ (⨅ i, (V i).comap (p i))) = _)
    have hoj := (hmem _).1 ho
    have h1 : prodF p V f [] ((1 : Γ) : Γ ⧸ (⨅ i, (V i).comap (p i))).out = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun j => ?_
      simp [fac, hoj j]
    rw [h1, one_mul, hg _ hoj]
  · intro q hq
    have hq' : ¬ ∀ j, p j q.out ∈ V j := by
      intro hall
      exact hq ((coset_one _ _).2 ((hmem _).2 hall))
    obtain ⟨j, hj⟩ := not_forall.1 hq'
    have h0 : prodF p V f [] q.out = 0 :=
      finprod_eq_zero _ j (by simp [fac, hj]) (fac_finite f hS [] q.out)
    rw [h0, zero_mul]

theorem sum_comp {p : ∀ i, Γ →* Hl i} {e : ∀ i, Hl i →* Γ} {KH V : ∀ i, Subgroup (Hl i)} {f : ∀ i, Hl i → ℂ}
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hS : ∀ x, ∀ᶠ j in cofinite, p j x ∈ V j)
    (hVK : ∀ i, V i ≤ KH i) (hVi : ∀ i, (V i).relIndex (KH i) ≠ 0)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hfs : ∀ i, {q : Hl i ⧸ V i | f i q.out ≠ 0}.Finite)
    (T : List ι) (hT : T.Nodup) (g : Γ → ℂ) (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x) (y : Γ) :
    ∑ᶠ q : Γ ⧸ (⨅ i, (V i).comap (p i)), prodF p V f T q.out * g (y * q.out) =
      (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod * comp e KH f g T y := by
  induction T generalizing y with
  | nil =>
    rw [sum_nil f hg hS y]
    simp [comp]
  | cons i T ih =>
    have hi : i ∉ T := (List.nodup_cons.1 hT).1
    have hT' : T.Nodup := (List.nodup_cons.1 hT).2
    have hmem : ∀ u ∈ (⨅ i, (V i).comap (p i)), ∀ j, p j u ∈ V j := by
      intro u hu j
      exact (Subgroup.mem_iInf.1 hu) j
    have hφ : ∀ u ∈ (⨅ i, (V i).comap (p i)), ∀ x,
        (fun x => prodF p V f (i :: T) x * g (y * x)) (x * u) =
          (fun x => prodF p V f (i :: T) x * g (y * x)) x := by
      intro u hu x
      change prodF p V f (i :: T) (x * u) * g (y * (x * u)) = prodF p V f (i :: T) x * g (y * x)
      rw [prodF_mul hfV _ _ _ (hmem u hu), ← mul_assoc, hg u (hmem u hu)]
    have hfin : {q : Γ ⧸ (⨅ i, (V i).comap (p i)) |
        (fun x => prodF p V f (i :: T) x * g (y * x)) q.out ≠ 0}.Finite := by
      refine (GlobalTheory.T.finite_restricted_product_quotient p V (fun j => {h | fac V f (i :: T) j h ≠ 0}) ?_ ?_ ?_).subset ?_
      · intro j x hx u hu
        change fac V f (i :: T) j (x * u) ≠ 0
        rw [fac_mul hfV _ _ _ _ hu]
        exact hx
      · intro j
        by_cases hj : j ∈ i :: T
        · refine (hfs j).subset fun q hq => ?_
          have hq' : fac V f (i :: T) j q.out ≠ 0 := hq
          simpa [fac, hj] using hq'
        · refine (Set.finite_singleton ((1 : Hl j) : Hl j ⧸ V j)).subset fun q hq => ?_
          have hq' : fac V f (i :: T) j q.out ≠ 0 := hq
          have hm : q.out ∈ V j := by
            by_contra hc
            exact hq' (by simp [fac, hj, hc])
          exact (coset_one _ _).2 hm
      · have : ∀ᶠ j in cofinite, j ∉ i :: T :=
          (List.finite_toSet (i :: T)).compl_mem_cofinite
        refine this.mono fun j hj h hh => ?_
        by_contra hc
        exact hh (by simp [fac, hj, show h ∉ V j from hc])
      · intro q hq j
        exact fac_ne_zero hS (i :: T) q.out (left_ne_zero_of_mul hq) j
    have h1 : ∑ᶠ q : Γ ⧸ (⨅ i, (V i).comap (p i)), prodF p V f (i :: T) q.out * g (y * q.out) =
        ∑ᶠ m : Hl i ⧸ V i, ∑ᶠ q : Γ ⧸ (⨅ i, (V i).comap (p i)),
          (V i : Set (Hl i)).indicator (1 : Hl i → ℂ) (p i q.out) *
            (prodF p V f (i :: T) (e i m.out * q.out) * g (y * (e i m.out * q.out))) :=
      GlobalTheory.T.finite_sum_fiber_decomposition (p i) (e i) (hpe i) (⨅ i, (V i).comap (p i)) (V i)
        (fun u hu => hmem u hu i) (fun x => prodF p V f (i :: T) x * g (y * x)) hφ hfin
    have inner : ∀ m : Hl i ⧸ V i, ∑ᶠ q : Γ ⧸ (⨅ i, (V i).comap (p i)),
        (V i : Set (Hl i)).indicator (1 : Hl i → ℂ) (p i q.out) *
          (prodF p V f (i :: T) (e i m.out * q.out) * g (y * (e i m.out * q.out))) =
        f i m.out * ((T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod *
          comp e KH f g T (y * e i m.out)) := by
      intro m
      rw [← ih hT' (y * e i m.out), ← smul_eq_mul, smul_finsum]
      refine finsum_congr fun q => ?_
      rw [smul_eq_mul, ← mul_assoc, prodF_split hpe hpe' hfV hS hi, mul_assoc, mul_assoc y]
    have hinv : V i ≤ rStab (fun m => f i m * comp e KH f g T (y * e i m)) := by
      intro v hv x
      change f i (x * v) * comp e KH f g T (y * e i (x * v)) = f i x * comp e KH f g T (y * e i x)
      rw [hfV i v hv x, map_mul, ← mul_assoc, comp_inv hpe hpe' hsep hg hv T hi]
    have hlev := GlobalTheory.CompanionTheory.HintLevel.hint_eq_level (Hl i) (KH i) (V i)
      (fun m => f i m * comp e KH f g T (y * e i m)) (hVK i) hinv (hVi i)
    have hr : (((V i).relIndex (KH i) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hVi i)
    have hcomp : comp e KH f g (i :: T) y = hint (KH i) (fun m => f i m * comp e KH f g T (y * e i m)) := rfl
    rw [h1, hcomp, hlev, List.map_cons, List.prod_cons, finsum_congr inner]
    have hpull : ∑ᶠ m : Hl i ⧸ V i, f i m.out * ((T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod *
          comp e KH f g T (y * e i m.out)) =
        (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod *
          ∑ᶠ m : Hl i ⧸ V i, f i m.out * comp e KH f g T (y * e i m.out) := by
      rw [← smul_eq_mul, smul_finsum]
      refine finsum_congr fun m => ?_
      simp only [smul_eq_mul]
      ring
    rw [hpull]
    field_simp

theorem sum_formula : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (KH V : ∀ i, Subgroup (Hl i)) (f : ∀ i, Hl i → ℂ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hev : ∀ x, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hVK : ∀ i, V i ≤ KH i) (hVi : ∀ i, (V i).relIndex (KH i) ≠ 0)
    (hVe : ∀ᶠ i in cofinite, V i = KH i)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hfs : ∀ i, {q : Hl i ⧸ V i | f i q.out ≠ 0}.Finite)
    (T : List ι) (hT : T.Nodup) (g : Γ → ℂ) (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x) (y : Γ),
    ∑ᶠ q : Γ ⧸ (⨅ i, (V i).comap (p i)),
        (∏ᶠ j, if j ∈ T then f j (p j q.out) else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j q.out)) * g (y * q.out) =
      (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod *
        T.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g y := by
  intro ι Γ _ Hl _ p e KH V f hpe hpe' hsep hev hVK hVi hVe hfV hfs T hT g hg y
  have hS : ∀ x, ∀ᶠ j in cofinite, p j x ∈ V j := fun x =>
    ((hev x).and hVe).mono fun j h => by rw [h.2]; exact h.1
  exact sum_comp hpe hpe' hsep hS hVK hVi hfV hfs T hT g hg y

end GlobalTheory.CompanionTheory.FinActSum

end
