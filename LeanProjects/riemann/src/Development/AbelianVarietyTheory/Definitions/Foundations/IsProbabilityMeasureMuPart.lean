import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SectionInputData

noncomputable section

namespace GlobalTheory.AllWt

open NumberField IsDedekindDomain MeasureTheory Module

section Gram

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

def IsGram {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : (K →+* ℂ) → V → ℝ) : Prop :=
  ∀ v, IsUnit (X v).det ∧ ∀ x, Formalism.HermitianLatticesTheory.normAt b X v x = N v.embedding x

def GramFr (N : (K →+* ℂ) → V → ℝ) : Type :=
  Σ n : ℕ, {p : Basis (Fin n) K V × (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) // IsGram p.1 p.2 N}

def HasGram (N : (K →+* ℂ) → V → ℝ) : Prop := Nonempty (GramFr N)

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

open Classical in

def slope_sq (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ :=
  letI : StarRing K := starRingOfComm
  if h : HasGram N then Formalism.HN.muDef h.some.2.1.1 h.some.2.1.2 L else 0

open Classical in

def slopeMax_sq (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ :=
  letI : StarRing K := starRingOfComm
  if h : HasGram N then Formalism.HN.muMaxDef h.some.2.1.1 h.some.2.1.2 L else 0

open Classical in

def slopeMin_sq (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ :=
  letI : StarRing K := starRingOfComm
  if h : HasGram N then Formalism.HN.muMinDef h.some.2.1.1 h.some.2.1.2 L else 0

def slope (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ := slope_sq N L / 2

def deg (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ := (Formalism.HN.rkK L : ℝ) * slope N L

section Indep

variable [StarRing K]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem norm_realize_sq {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, sq]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem IsGram.norm_realize {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V}
    {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Basis κ K V} {X' : InfinitePlace K → Matrix κ κ ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (h' : IsGram b' X' N) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ = ‖Formalism.HermitianLatticesTheory.realize b' X' x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_realize_sq, norm_realize_sq]
  exact Finset.sum_congr rfl fun v _ => by rw [(h v).2, (h' v).2]

theorem IsGram.rk_deg {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V}
    {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Basis κ K V} {X' : InfinitePlace K → Matrix κ κ ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (h' : IsGram b' X' N) {L : Submodule (𝓞 K) V} (hL : L.FG) :
    Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) L = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b' X') L ∧
      Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L = Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b' X') L := by
  obtain ⟨h1, h2, -⟩ := Formalism.HN.plLat K V ι b X (fun v => (h v).1) L hL
  obtain ⟨h1', h2', -⟩ := Formalism.HN.plLat K V κ b' X' (fun v => (h' v).1) L hL
  refine ⟨h2.trans h2'.symm, ?_⟩
  haveI := h1.2
  haveI := h1'.2
  unfold Formalism.HN.deg Formalism.F.deg
  rw [Formalism.HN.QuotientRealization.covol_eq_of_norm_eq ((Formalism.HermitianLatticesTheory.realize b X).comp L.toAddSubgroup.subtype)
    ((Formalism.HermitianLatticesTheory.realize b' X').comp L.toAddSubgroup.subtype) (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)
    (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b' X') L)
    (fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩)
    (fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩)
    (fun m => h.norm_realize h' m.1)]

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem IsGram.hasGram {ι : Type} [Fintype ι] [DecidableEq ι] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) : HasGram N := by
  let e := Fintype.equivFin ι
  refine ⟨⟨_, ⟨(b.reindex e, fun v => Matrix.reindex e e (X v)), fun v => ⟨?_, fun x => ?_⟩⟩⟩⟩
  · simpa using (h v).1
  · rw [← (h v).2 x]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    rw [Matrix.inv_reindex]
    simp only [Matrix.mulVec, dotProduct]
    rw [← e.sum_comp]
    simp [Formalism.HermitianLatticesTheory.vecAt]

theorem slope_sq_eq {ι : Type} [Fintype ι] [DecidableEq ι] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) {L : Submodule (𝓞 K) V} (hL : L.FG) :
    slope_sq N L = Formalism.HN.muDef b X L := by
  rw [slope_sq, dif_pos h.hasGram]
  show Formalism.HN.muDef h.hasGram.some.2.1.1 h.hasGram.some.2.1.2 L = _
  obtain ⟨h1, h2⟩ := IsGram.rk_deg h.hasGram.some.2.2 h hL
  unfold Formalism.HN.rk at h1
  unfold Formalism.HN.deg at h2
  unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
  rw [h1, h2]

theorem slopeMax_slopeMin_eq {ι : Type} [Fintype ι] [DecidableEq ι] {b : Basis ι K V}
    {X : InfinitePlace K → Matrix ι ι ℂ} {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) {L : Submodule (𝓞 K) V}
    (hL : L.FG) (h0 : L ≠ ⊥) :
    slopeMax_sq N L = Formalism.HN.muMaxDef b X L ∧ slopeMin_sq N L = Formalism.HN.muMinDef b X L := by
  have h' := h.hasGram.some.2.2
  have key := (Formalism.HN.shiftInvariance (𝓞 K) V _ _ _ _ L 0
    (Formalism.HN.plLat K V ι b X (fun v => (h v).1) L hL).1
    (Formalism.HN.plLat K V _ _ _ (fun v => (h' v).1) L hL).1
    (fun M hM => by
      have hM' : M.FG := by
        haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
        exact isNoetherian_submodule.1 inferInstance M hM
      simpa using IsGram.rk_deg h' h hM')).2.1 h0
  rw [slopeMax_sq, slopeMin_sq, dif_pos h.hasGram, dif_pos h.hasGram]
  show Formalism.HN.muMaxDef h.hasGram.some.2.1.1 h.hasGram.some.2.1.2 L = _ ∧
    Formalism.HN.muMinDef h.hasGram.some.2.1.1 h.hasGram.some.2.1.2 L = _
  unfold Formalism.HN.muMaxDef Formalism.HN.muMinDef
  rw [key.1, key.2, add_zero, add_zero]
  exact ⟨rfl, rfl⟩

end Indep

theorem deg_bot (N : (K →+* ℂ) → V → ℝ) : deg N (⊥ : Submodule (𝓞 K) V) = 0 := by
  simp [deg, Formalism.HN.rkK]

theorem slope_sq_line [IsTotallyComplex K] (x : K) (hx : x ≠ 0) :
    slope_sq (fun (σ : K →+* ℂ) (y : K) => ‖σ y‖) (Submodule.span (𝓞 K) {x}) =
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v : InfinitePlace K, 2 * Real.log (v x)) := by
  letI : StarRing K := starRingOfComm
  have hn : ∀ v y, Formalism.HermitianLatticesTheory.normAt (Basis.singleton Unit K) (fun _ : InfinitePlace K => (1 : Matrix Unit Unit ℂ)) v y =
      ‖v.embedding y‖ := fun v y => by
    simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt]
  have h : IsGram (Basis.singleton Unit K) (fun _ : InfinitePlace K => (1 : Matrix Unit Unit ℂ))
      (fun (σ : K →+* ℂ) (y : K) => ‖σ y‖) := fun v => ⟨by simp, hn v⟩
  rw [slope_sq_eq h (Submodule.fg_span (Set.finite_singleton x)),
    Formalism.ExtensionFiltration.muDef_line_eq _ _ (fun v => (h v).1) x hx]
  simp [hn, InfinitePlace.norm_embedding_eq]

example [IsTotallyComplex K] :
    slope_sq (fun (σ : K →+* ℂ) (y : K) => ‖σ y‖) (Submodule.span (𝓞 K) {(1 : K)}) = 0 := by
  rw [slope_sq_line 1 one_ne_zero]; simp

end Gram

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

abbrev Psi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Type := {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}

abbrev Weight (Dw : Datum H) : Type := Psi H → Fin (Dw.p + Dw.q) → ℤ

open Classical in

def wtOf (Dw : Datum H) (la : Weight Dw) (m : ℤ) : WTZ E :=
  (fun x =>
    if h : x.1 (H.rt : E) = H.rt0 then
      (if hi : x.2 < Dw.p then la ⟨x.1, h⟩ ⟨x.2, by omega⟩ - m else 0)
    else if h' : conjEmb x.1 (H.rt : E) = H.rt0 then
      (if hi : x.2 < Dw.q then -la ⟨conjEmb x.1, h'⟩ ⟨Dw.p + (Dw.q - 1 - x.2), by omega⟩ - m else 0)
    else 0, 2 * m)

def exOf (Dw : Datum H) (la : Weight Dw) (m : ℤ) : Ix Dw → ℤ := exZ Dw (wtOf Dw la m)

theorem wtOf_snd (la : Weight Dw) (m : ℤ) : (wtOf Dw la m).2 = 2 * m := rfl

theorem even_wtOf (la : Weight Dw) (m : ℤ) : Even (wtOf Dw la m).2 := even_two_mul m

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext a; simp [conjEmb]

theorem conj_not_mem (τ : Psi H) : ¬ conjEmb τ.1 (H.rt : E) = H.rt0 := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have : starRingEnd ℂ (τ.1 (H.rt : E)) = H.rt0 := h'
    rwa [τ.2] at this
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, him, Complex.neg_re, Complex.natCast_re] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

theorem wtOf_big (la : Weight Dw) (m : ℤ) (τ : Psi H) (i : ℕ) (hi : i < Dw.p) :
    (wtOf Dw la m).1 (τ.1, i) = la τ ⟨i, by omega⟩ - m := by
  simp only [wtOf, dif_pos τ.2, dif_pos hi]

theorem wtOf_small (la : Weight Dw) (m : ℤ) (τ : Psi H) (i : ℕ) (hi : i < Dw.q) :
    (wtOf Dw la m).1 (conjEmb τ.1, i) = -la τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ - m := by
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by rw [conjEmb_conjEmb]; exact τ.2
  have e : (⟨conjEmb (conjEmb τ.1), h'⟩ : Psi H) = τ := Subtype.ext (conjEmb_conjEmb _)
  simp only [wtOf, dif_neg (conj_not_mem τ), dif_pos h', dif_pos hi, e]

theorem wtOf_add (la la' : Weight Dw) (m m' : ℤ) :
    wtOf Dw (la + la') (m + m') = wtOf Dw la m + wtOf Dw la' m' := by
  refine Prod.ext (funext fun x => ?_) (by simp only [wtOf, Prod.snd_add]; ring)
  simp only [wtOf, Prod.fst_add, Pi.add_apply]
  split_ifs <;> ring

theorem wtOf_zero : wtOf Dw 0 0 = 0 := by
  refine Prod.ext (funext fun x => ?_) (by simp [wtOf])
  simp [wtOf]

theorem exOf_add (la la' : Weight Dw) (m m' : ℤ) :
    exOf Dw (la + la') (m + m') = exOf Dw la m + exOf Dw la' m' := by
  funext i; rw [exOf, wtOf_add, exZ_add]; rfl

theorem exZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : exZ Dw (wtZ a n) = fun i => (ex Dw a n i : ℤ) := by
  funext i; cases i <;> rfl

def weightOf (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℤ) (m : ℤ) : Weight Dw :=
  fun τ j => if (j : ℕ) < Dw.p then a (τ.1, j) + m else -a (conjEmb τ.1, Dw.q - 1 - ((j : ℕ) - Dw.p)) - m

theorem weightOf_wtOf (la : Weight Dw) (m : ℤ) : weightOf Dw (wtOf Dw la m).1 m = la := by
  funext τ j
  have hj := j.2
  unfold weightOf
  split_ifs with h
  · rw [wtOf_big la m τ j h]; simp
  · rw [wtOf_small la m τ _ (by omega)]
    have : (⟨Dw.p + (Dw.q - 1 - (Dw.q - 1 - ((j : ℕ) - Dw.p))), by omega⟩ : Fin (Dw.p + Dw.q)) = j :=
      Fin.ext (by simp only; omega)
    rw [this]; ring

theorem conj_mem {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) = H.rt0 := by
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
  have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have him := congrArg Complex.im H.sqrt_neg_disc_sq
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hne
    rw [this] at hre; nlinarith [mul_self_nonneg H.rt0.re]
  change (starRingEnd ℂ) (τ (H.rt : E)) = H.rt0
  rw [h3]
  apply Complex.ext <;> simp [h0]

theorem exOf_weightOf (a : (E →+* ℂ) × ℕ → ℤ) (m : ℤ) : exOf Dw (weightOf Dw a m) m = exZ Dw (a, 2 * m) := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · rfl
  · show (wtOf Dw (weightOf Dw a m) m).1 (τ, i) = a (τ, i)
    have hi := i.2
    by_cases h : τ (H.rt : E) = H.rt0
    · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
      rw [wtOf_big _ m ⟨τ, h⟩ i hp]
      simp [weightOf, hp]
    · have hq : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
      have e := wtOf_small (weightOf Dw a m) m ⟨conjEmb τ, conj_mem h⟩ i hq
      simp only [conjEmb_conjEmb] at e
      rw [e]
      have h1 : ¬ Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p := by omega
      have h2 : Dw.q - 1 - (Dw.p + (Dw.q - 1 - (i : ℕ)) - Dw.p) = i := by omega
      simp only [weightOf, h1, if_false, h2, conjEmb_conjEmb]
      ring

example (w : ℤ) (τ : Psi H) (i j : ℕ) (hi : i < Dw.p) (hj : j < Dw.q) :
    (wtOf Dw (fun _ _ => w) 0).1 (τ.1, i) = w ∧ (wtOf Dw (fun _ _ => w) 0).1 (conjEmb τ.1, j) = -w := by
  rw [wtOf_big _ _ _ _ hi, wtOf_small _ _ _ _ hj]; simp

example (τ : Psi H) (i j : ℕ) (hi : i < Dw.p) (hj : j < Dw.q) :
    (wtOf Dw (fun _ k => if (k : ℕ) < Dw.p then 0 else -1) 0).1 (τ.1, i) = 0 ∧
      (wtOf Dw (fun _ k => if (k : ℕ) < Dw.p then 0 else -1) 0).1 (conjEmb τ.1, j) = 1 := by
  rw [wtOf_big _ _ _ _ hi, wtOf_small _ _ _ _ hj]; simp [hi]

variable (Xo : Moduli Dw l) (c : Coeff l)

set_option synthInstance.maxHeartbeats 400000 in

def secZ (e : Ix Dw → ℤ) : Submodule c.F (Rul Xo c) where
  carrier := {f | IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
    ∀ (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R), FrBor t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp only [Pi.add_apply, hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun a f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp only [Pi.smul_apply, hf.2 p t y y' h, mul_smul_comm]⟩

variable {Xo c}

theorem mem_secZ {e : Ix Dw → ℤ} {f : Rul Xo c} : f ∈ secZ Xo c e ↔
    IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
    ∀ (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R), FrBor t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y := Iff.rfl

theorem mem_secZ_exZ {G : WTZ E} {f : Rul Xo c} : f ∈ secZ Xo c (exZ Dw G) ↔ GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.IsSecZ G f := Iff.rfl

variable (Xo c) in

theorem secZ_nat (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : secZ Xo c (fun i => (ex Dw a n i : ℤ)) = sec Xo c a n := by
  ext f
  rw [← exZ_wtZ, mem_secZ_exZ, GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.isSecZ_wtZ]

theorem mul_mem_secZ {e e' : Ix Dw → ℤ} {f g : Rul Xo c} (hf : f ∈ secZ Xo c e) (hg : g ∈ secZ Xo c e') :
    f * g ∈ secZ Xo c (e + e') := by
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · show f q z * g q z = φ (f p y * g p y)
    rw [hf.1 p q φ y z h, hg.1 p q φ y z h, map_mul]
  · show f p y' * g p y' = _ * (f p y * g p y)
    rw [hf.2 p t y y' h, hg.2 p t y y' h]
    simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
    ring

variable (Xo c) in

theorem secZ_mul_le (e e' : Ix Dw → ℤ) : secZ Xo c e * secZ Xo c e' ≤ secZ Xo c (e + e') :=
  Submodule.mul_le.2 fun _ hf _ hg => mul_mem_secZ hf hg

theorem one_mem_secZ : (1 : Rul Xo c) ∈ secZ Xo c 0 :=
  ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩

theorem inv_mem_secZ {e : Ix Dw → ℤ} {u : (Rul Xo c)ˣ} (hu : (u : Rul Xo c) ∈ secZ Xo c e) :
    ((u⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) ∈ secZ Xo c (-e) := by
  have h1 : ∀ p y, (u : Rul Xo c) p y * (u⁻¹ : (Rul Xo c)ˣ).val p y = 1 := fun p y =>
    congrFun (congrFun u.mul_inv p) y
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · have a1 := h1 q z
    have a2 := congrArg φ (h1 p y)
    rw [map_mul, map_one, ← hu.1 p q φ y z h] at a2
    linear_combination (φ ((u⁻¹ : (Rul Xo c)ˣ).val p y)) * a1 - ((u⁻¹ : (Rul Xo c)ˣ).val q z) * a2
  · have a1 := h1 p y'
    have a2 := h1 p y
    rw [hu.2 p t y y' h] at a1
    have a3 : ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) * ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]; simp
    generalize ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) = A at *
    generalize ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = B at *
    generalize (u⁻¹ : (Rul Xo c)ˣ).val p y' = v' at *
    generalize (u⁻¹ : (Rul Xo c)ˣ).val p y = v at *
    generalize (u : Rul Xo c) p y = w at *
    linear_combination (A * v) * a1 - (A * B * v') * a2 - v' * a3

section Cusp

variable {r : ℕ}

open Classical in

def modelWt {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (G : WTZ E) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then
      G.1 (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) + G.2 / 2
    else -G.1 (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) - G.2 / 2

theorem modelWt_wtZ {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    modelWt U (wtZ a n) = laU U a n := by
  funext k τ i
  simp only [modelWt, wtZ, laU, Int.natCast_div, Nat.cast_ofNat]

theorem modelWt_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2)
    (k : U.Comp) : modelWt U (G + G') k = modelWt U G k + modelWt U G' k := by
  funext τ i
  obtain ⟨a, ha⟩ := hG
  obtain ⟨b, hb⟩ := hG'
  simp only [modelWt, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> omega

theorem relab_injective (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := fun τ τ' h => by
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

theorem relab_conj (σ : c.F →+* ℂ) (τ : E →+* ℂ) : relab c σ (conjEmb τ) = conjEmb (relab c σ τ) := by
  ext a
  have h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm
  show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (relab c σ τ) a

theorem modelWt_wtOf_big {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (la : Weight Dw) (m : ℤ) (k : U.Comp)
    (hq : (U.X k).p0 = Dw.q) (τ : Psi H) (hτ : relab c σ τ.1 ∈ (U.X k).Ψ) (i : ℕ) (hi : i < Dw.p)
    (hr : Dw.q + i < r) : modelWt U (wtOf Dw la m) k ⟨_, hτ⟩ ⟨_, hr⟩ = la τ ⟨i, by omega⟩ := by
  simp only [modelWt, hq, Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
    Function.leftInverse_invFun (relab_injective σ) τ.1, wtOf_big la m τ i hi, wtOf_snd]
  omega

theorem modelWt_wtOf_small {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (la : Weight Dw) (m : ℤ) (k : U.Comp)
    (hq : (U.X k).p0 = Dw.q) (τ : Psi H) (hτ : relab c σ τ.1 ∈ (U.X k).Ψ) (j : ℕ) (hj : j < Dw.q)
    (hr : j < r) : modelWt U (wtOf Dw la m) k ⟨_, hτ⟩ ⟨_, hr⟩ = la τ ⟨Dw.p + j, by omega⟩ := by
  have h1 : ¬ Dw.q ≤ j := by omega
  have h2 : Dw.q - 1 - (Dw.q - 1 - j) = j := by omega
  simp only [modelWt, hq, h1, if_false, ← relab_conj,
    Function.leftInverse_invFun (relab_injective σ) (conjEmb τ.1), wtOf_small la m τ (Dw.q - 1 - j) (by omega),
    wtOf_snd, h2]
  omega

variable (Xo c) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspW (G : WTZ E) : Submodule c.F (Rul Xo c) :=
  secZ Xo c (exZ Dw G) ⊓
    ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (modelWt (U σ) G)).comap (rdU (U σ))

def cuspZ (la : Weight Dw) (m : ℤ) : Submodule c.F (Rul Xo c) := cuspW Xo c U (wtOf Dw la m)

variable {Xo c U}

theorem mem_cuspW {G : WTZ E} {f : Rul Xo c} : f ∈ cuspW Xo c U G ↔ f ∈ secZ Xo c (exZ Dw G) ∧
    ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (modelWt (U σ) G) := by
  simp [cuspW, Submodule.mem_iInf]

theorem cuspW_le_secZ (G : WTZ E) : cuspW Xo c U G ≤ secZ Xo c (exZ Dw G) := inf_le_left

theorem cuspW_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cuspW Xo c U (wtZ a n) = cusp Xo c U a n := by
  simp only [cuspW, cusp, exZ_wtZ, secZ_nat, modelWt_wtZ]

theorem modelWt_congr {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') : modelWt U G = modelWt U G' := by
  funext k τ j
  have h2 : G.2 = G'.2 := congrFun h none
  have h1 : ∀ (ρ : E →+* ℂ) (i : ℕ), i < Dw.mult ρ → G.1 (ρ, i) = G'.1 (ρ, i) := fun ρ i hi =>
    congrFun h (some ⟨ρ, ⟨i, hi⟩⟩)
  have hsurj : Function.Surjective (relab (E := E) c σ) := Finite.injective_iff_surjective.1 (relab_injective σ)
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hr := hU.1
  have hj := j.2
  obtain ⟨ρ, hρ⟩ := hsurj τ.1
  have hρΨ : ρ (H.rt : E) = H.rt0 := by
    by_contra hn
    have h3 : relab c σ (conjEmb ρ) (H.rt : E) = H.rt0 := by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext (conj_mem hn))).trans hσ0
    rw [relab_conj, hρ] at h3
    exact conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
  have e1 : Function.invFun (relab c σ) τ.1 = ρ := by
    rw [← hρ]; exact Function.leftInverse_invFun (relab_injective σ) ρ
  have e2 : Function.invFun (relab c σ) (conjEmb τ.1) = conjEmb ρ := by
    rw [← hρ, ← relab_conj]; exact Function.leftInverse_invFun (relab_injective σ) _
  unfold modelWt
  rw [e1, e2, h2]
  split_ifs with hj'
  · rw [h1 ρ _ (by rw [Datum.mult, if_pos hρΨ]; omega)]
  · rw [h1 (conjEmb ρ) _ (by rw [Datum.mult, if_neg (conj_not_mem ⟨ρ, hρΨ⟩)]; omega)]

theorem cuspZ_weightOf (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) :
    cuspZ Xo c U (weightOf Dw (fun x => (a x : ℤ)) m) m = cusp Xo c U a (2 * m) := by
  have h : exZ Dw (wtOf Dw (weightOf Dw (fun x => (a x : ℤ)) m) m) = exZ Dw (wtZ a (2 * m)) := by
    have := exOf_weightOf (Dw := Dw) (fun x => (a x : ℤ)) m
    rw [exOf] at this
    rw [this, wtZ]; push_cast; rfl
  rw [← cuspW_wtZ]
  ext f
  rw [cuspZ, mem_cuspW, mem_cuspW, h]
  exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

end Cusp

def ptF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, sOf, ← Spec.map_comp]; rfl)

def LiesOn (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  ∀ s : Sp S, ptF y s ∈ (Z : Set (Xo.XF c))

def LiesOff (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  ∀ s : Sp S, ptF y s ∉ (Z : Set (Xo.XF c))

theorem liesOff_iff (Z : Comp Xo c) {S : Type} [Field S] [Algebra c.F S] (y : FrPt Xo c S) :
    LiesOff Z y ↔ ¬ LiesOn Z y := by
  have hs : ∀ s s' : Sp S, s = s' := fun s s' => Subsingleton.elim (α := PrimeSpectrum S) s s'
  have s₀ : Sp S := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S)
  exact ⟨fun h h' => h s₀ (h' s₀), fun h s hs' => h fun s' => hs s s' ▸ hs'⟩

def suppOn (Z : Comp Xo c) : Submodule c.F (Rul Xo c) where
  carrier := {f | ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOff Z y → evR Xo c f y = 0}
  zero_mem' := fun S _ _ y _ => evalAt_zero _ _ y
  add_mem' := fun {f g} hf hg S _ _ y h => by
    have := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g y
    exact this.trans ((congrArg₂ (· + ·) (hf S y h) (hg S y h)).trans (add_zero 0))
  smul_mem' := fun a f hf S _ _ y h => by
    have := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) a f y
    exact this.trans ((congrArg (algebraMap c.F S a * ·) (hf S y h)).trans (mul_zero _))

theorem mem_suppOn {Z : Comp Xo c} {f : Rul Xo c} : f ∈ suppOn Z ↔
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOff Z y → evR Xo c f y = 0 := Iff.rfl

theorem mul_mem_suppOn {Z : Comp Xo c} (g : Rul Xo c) {f : Rul Xo c} (hf : f ∈ suppOn Z) : g * f ∈ suppOn Z :=
  fun S _ _ y h => by
    have := evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g f y
    exact this.trans ((congrArg (evR Xo c g y * ·) (hf S y h)).trans (mul_zero _))

theorem ptF_genFr (h : GenFrEx Xo c) (Z : Comp Xo c) (s : Sp (Om Z)) : ptF (genFr h Z) s = genPt Z := by
  have e : ptF (genFr h Z) = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, (isGenFr_genFr h Z).1, Category.assoc]; rfl
    · rw [ptF, pullback.lift_snd, Category.assoc]
      have h1 : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) := (Spec.map_preimage _).symm
      refine Eq.trans ?_ (congrArg (spMap (algebraMap (kap Z) (Om Z)) ≫ ·) h1.symm)
      show _ = spMap (algebraMap (kap Z) (Om Z)) ≫ spMap (algebraMap c.F (kap Z))
      rw [← Spec.map_comp, IsScalarTower.algebraMap_eq c.F (kap Z) (Om Z)]; rfl
  rw [e, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem liesOn_genFr (h : GenFrEx Xo c) (Z : Comp Xo c) : LiesOn Z (genFr h Z) := fun s => by
  rw [ptF_genFr]
  exact ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ Z.2)).mem

theorem liesOff_genFr (h : GenFrEx Xo c) {Z Z' : Comp Xo c} (hne : Z' ≠ Z) : LiesOff Z (genFr h Z') := fun s hs => by
  rw [ptF_genFr] at hs
  have hg := (Z'.2.1 : IsIrreducible (Z' : Set (Xo.XF c))).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ Z'.2)
  have hle : (Z' : Set (Xo.XF c)) ⊆ Z := (hg.mem_closed_set_iff (isClosed_of_mem_irreducibleComponents _ Z.2)).1 hs
  exact hne (Subtype.ext (hle.antisymm (Z'.2.2 Z.2.1 hle)))

theorem evC_eq_zero (h : GenFrEx Xo c) {Z Z' : Comp Xo c} (hne : Z' ≠ Z) {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    evC h Z' f = 0 :=
  hf _ _ (liesOff_genFr h hne)

example (h : GenFrEx Xo c) (ht : GenFromTest Xo c h) {Z Z' : Comp Xo c} (hne : Z' ≠ Z) :
    (1 : Rul Xo c) ∉ suppOn Z := fun h1 =>
  one_ne_zero ((evalAt_one _ _ _ (ht Z')).symm.trans (evC_eq_zero h hne h1))

section Inst

abbrev subModuleInt {K R : Type} [Field K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]
    (C : Submodule K R) : Module (𝓞 K) C := inferInstance

theorem subTower {K R : Type} [Field K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]
    (C : Submodule K R) : IsScalarTower (𝓞 K) K C := inferInstance

variable {K : Type} [Field K] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type) (C : Submodule K (Rules pts))

instance (priority := high) subRulesModuleInt : Module (𝓞 K) C := subModuleInt C

instance (priority := high) subRulesTower :
    @IsScalarTower (𝓞 K) K C Algebra.toSMul _ (subRulesModuleInt pts C).toSMul := subTower C

end Inst

section Lattices

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspOn (Z : Comp Xo c) (G : WTZ E) : Submodule c.F (Rul Xo c) := cuspW Xo c U G ⊓ suppOn Z

theorem cuspOn_le (Z : Comp Xo c) (G : WTZ E) : cuspOn U Z G ≤ cuspW Xo c U G := inf_le_left

def supLat (C : Submodule c.F (Rul Xo c)) : Submodule (𝓞 c.F) C :=
  latOf C (valSet Xo c (algCls Xo c)) isVal_valSet

theorem mem_supLat {C : Submodule c.F (Rul Xo c)} {f : C} :
    f ∈ supLat C ↔ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (f : Rul Xo c) := Iff.rfl

theorem mul_mem_supLat {C C' C'' : Submodule c.F (Rul Xo c)} {f : C} {g : C'} (hf : f ∈ supLat C)
    (hg : g ∈ supLat C') (h : (f : Rul Xo c) * g ∈ C'') : (⟨_, h⟩ : C'') ∈ supLat C'' := fun la v hv => by
  show 0 ≤ v ((f : Rul Xo c) * g)
  rw [(isVal_valSet la v hv).mul]
  exact add_nonneg (hf la v hv) (hg la v hv)

def latW (G : WTZ E) : Submodule (𝓞 c.F) (cuspW Xo c U G) := supLat _

def latOn (Z : Comp Xo c) (G : WTZ E) : Submodule (𝓞 c.F) (cuspOn U Z G) := supLat _

def latZ (la : Weight Dw) (m : ℤ) : Submodule (𝓞 c.F) (cuspW Xo c U (wtOf Dw la m)) := latW U (wtOf Dw la m)

theorem mem_latOn {Z : Comp Xo c} {G : WTZ E} {f : cuspOn U Z G} :
    f ∈ latOn U Z G ↔ (⟨f, cuspOn_le U Z G f.2⟩ : cuspW Xo c U G) ∈ latW U G := Iff.rfl

end Lattices

section Model

variable {r : ℕ} {Cp : Type} {X : Cp → Data E r} {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)

def ptN (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) (z : Σ k, Frame (X k).Ψ r) : ℝ := (X z.1).pnorm (la z.1) (P z.1) z.2

theorem ptN_nonneg (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) (z : Σ k, Frame (X k).Ψ r) : 0 ≤ ptN la P z :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg _ _ _)

def classesOver (A : Set (Σ k, Frame (X k).Ψ r)) : Set (AutQ V) := {q | dict q.out ∈ A}

def muPart (A : Set (Σ k, Frame (X k).Ψ r)) : Measure (AutQ V) := ProbabilityTheory.cond (muQ1 V) (classesOver V dict A)

def muComp (k : Cp) : Measure (AutQ V) := muPart V dict {z | z.1 = k}

theorem isProbabilityMeasure_muPart {A : Set (Σ k, Frame (X k).Ψ r)} (h : muQ1 V (classesOver V dict A) ≠ 0) :
    IsProbabilityMeasure (muPart V dict A) :=
  ProbabilityTheory.cond_isProbabilityMeasure h

theorem muPart_univ : muPart V dict Set.univ = muQ1 V := by
  have : classesOver V dict Set.univ = Set.univ := rfl
  rw [muPart, this, ProbabilityTheory.cond_univ]

theorem muPart_univ_le (A : Set (Σ k, Frame (X k).Ψ r)) : muPart V dict A Set.univ ≤ 1 := by
  haveI : IsZeroOrProbabilityMeasure (muPart V dict A) := by unfold muPart; infer_instance
  exact prob_le_one

variable (μ : Measure (AutQ V))

def petE (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) : ENNReal := eLpNorm (fun q : AutQ V => ptN la P (dict q.out)) 2 μ

theorem petE_smul (la : ∀ k, Wt (X k).Ψ r) (a : ℂ) (P : FDSec X) :
    petE V dict μ la (a • P) = ENNReal.ofReal ‖a‖ * petE V dict μ la P := by
  have : (fun q : AutQ V => ptN la (a • P) (dict q.out)) = ‖a‖ • fun q : AutQ V => ptN la P (dict q.out) :=
    funext fun q => pnorm_smul _ _ a _ _
  rw [petE, this, eLpNorm_const_smul, petE, Real.enorm_eq_ofReal (norm_nonneg a)]

theorem petE_le_supE (hμ : μ Set.univ ≤ 1) (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (la : ∀ k, Wt (X k).Ψ r)
    (P : FDSec X) : petE V dict μ la P ≤ supE X la P := by
  have h : ∀ q : AutQ V, ‖ptN la P (dict q.out)‖ₑ ≤ supE X la P := fun q => by
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _)]
    exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2))
      ⟨(dict q.out).1, ⟨(dict q.out).2, hd _⟩⟩
  refine (eLpNorm_le_of_ae_enorm_bound (Filter.Eventually.of_forall h)).trans ?_
  rw [smul_eq_mul]
  refine (mul_le_mul_right (ENNReal.rpow_le_one hμ (by positivity)) _).trans (by simp)

theorem petE_ne_top [Fintype Cp] (hμ : μ Set.univ ≤ 1) (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom)
    {la : ∀ k, Wt (X k).Ψ r} {P : FDSec X} (hP : P ∈ holSub X la) : petE V dict μ la P ≠ ⊤ :=
  ne_top_of_le_ne_top (supE_ne_top X la hP) (petE_le_supE V dict μ hμ hd la P)

def bergE (la : ∀ k, Wt (X k).Ψ r) (y : FPt X) : ENNReal :=
  ⨆ P ∈ holSub X la, ENNReal.ofReal (ptN la P ⟨y.1, y.2.1⟩) ^ 2 / petE V dict μ la P ^ 2

theorem bergE_le_iff {la : ∀ k, Wt (X k).Ψ r} (hfin : ∀ P ∈ holSub X la, petE V dict μ la P ≠ ⊤) (y : FPt X) {B : ENNReal} (hB : B ≠ ⊤) :
    bergE V dict μ la y ≤ B ↔
      ∀ P ∈ holSub X la, ENNReal.ofReal (ptN la P ⟨y.1, y.2.1⟩) ^ 2 ≤ B * petE V dict μ la P ^ 2 := by
  simp only [bergE, iSup_le_iff]
  exact forall₂_congr fun P hP =>
    ENNReal.div_le_iff_le_mul (Or.inr hB) (Or.inl (ENNReal.pow_ne_top (hfin P hP)))

end Model

section Norms

variable {r : ℕ}

def lieFacZ (Dw : Datum H) (x : ℝ) (G : WTZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (G.1 (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFacZ_pos (x : ℝ) (G : WTZ E) : 0 < lieFacZ Dw x G := Real.exp_pos _

theorem lieFacZ_wtZ (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : lieFacZ Dw x (wtZ a n) = lieFac Dw x a := by
  simp [lieFacZ, lieFac, wtZ]

theorem lieFacZ_add (x : ℝ) (G G' : WTZ E) : lieFacZ Dw x (G + G') = lieFacZ Dw x G * lieFacZ Dw x G' := by
  simp only [lieFacZ, ← Real.exp_add, Prod.fst_add, Pi.add_apply, Int.cast_add, Finset.sum_add_distrib]
  congr 1; ring

section One

variable {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)

def homN (G : WTZ E) (f : Rul Xo c) (z : Σ k, Frame (U.X k).Ψ r) : ℝ :=
  lieFacZ Dw x G * ptN (modelWt U G) (rdU U f) z

theorem homN_nonneg (G : WTZ E) (f : Rul Xo c) (z : Σ k, Frame (U.X k).Ψ r) : 0 ≤ homN U x G f z :=
  mul_nonneg (lieFacZ_pos _ _).le (ptN_nonneg _ _ _)

theorem rdU_mul (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k y
  by_cases h : y ∈ (U.X k).dom
  · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply, h, dif_pos]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨y, h⟩)
  · simp [rdU, h]

theorem homN_mul {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) (f g : Rul Xo c) (z : Σ k, Frame (U.X k).Ψ r)
    (hz : z.2 ∈ (U.X z.1).dom) : homN U x (G + G') (f * g) z = homN U x G f z * homN U x G' g z := by
  have hd : ∀ τ i, dmin (U.X z.1).Gm z.2 τ i ≠ 0 := fun τ i h0 => by
    have := (hz τ).2 i
    rw [h0] at this; simp at this
  have key : ∀ la la' : Wt (U.X z.1).Ψ r, (U.X z.1).nfac (la + la') z.2 =
      (U.X z.1).nfac la z.2 * (U.X z.1).nfac la' z.2 := fun la la' => by
    unfold Data.nfac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _)))]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  show _ * (‖rdU U (f * g) z.1 z.2‖ * (U.X z.1).nfac (modelWt U (G + G') z.1) z.2) =
    _ * (‖rdU U f z.1 z.2‖ * (U.X z.1).nfac (modelWt U G z.1) z.2) *
      (_ * (‖rdU U g z.1 z.2‖ * (U.X z.1).nfac (modelWt U G' z.1) z.2))
  rw [modelWt_add U hG hG', key, lieFacZ_add, rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul]
  ring

def framesOn (Z : Comp Xo c) : Set (Σ k, Frame (U.X k).Ψ r) :=
  {z | ∃ h : z.2 ∈ (U.X z.1).dom, LiesOn Z (U.un z.1 ⟨z.2, h⟩)}

theorem rdU_eq_zero {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) {z : Σ k, Frame (U.X k).Ψ r}
    (hz : z ∉ framesOn U Z) : rdU U f z.1 z.2 = 0 := by
  by_cases h : z.2 ∈ (U.X z.1).dom
  · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, h, dif_pos]
    refine hf (CAt σ) _ fun s hs => hz ⟨h, fun s' => ?_⟩
    have : s = s' := Subsingleton.elim (α := PrimeSpectrum ℂ) s s'
    exact this ▸ hs
  · simp [rdU, h]

variable {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)

def muOn (Z : Comp Xo c) : Measure (AutQ V) := muPart V dict (framesOn U Z)

variable (μ : Measure (AutQ V))

def petAt (G : WTZ E) (f : Rul Xo c) : ℝ := lieFacZ Dw x G * (petE V dict μ (modelWt U G) (rdU U f)).toReal

theorem petAt_nonneg (G : WTZ E) (f : Rul Xo c) : 0 ≤ petAt U x V dict μ G f :=
  mul_nonneg (lieFacZ_pos _ _).le ENNReal.toReal_nonneg

theorem petAt_smul (G : WTZ E) (a : c.F) (f : Rul Xo c) :
    petAt U x V dict μ G (a • f) = ‖σ a‖ * petAt U x V dict μ G f := by
  unfold petAt
  rw [map_smulₛₗ, petE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  ring

theorem petAt_eq (G : WTZ E) (f : Rul Xo c) :
    petAt U x V dict μ G f = (eLpNorm (fun q : AutQ V => homN U x G f (dict q.out)) 2 μ).toReal := by
  have : (fun q : AutQ V => homN U x G f (dict q.out)) =
      lieFacZ Dw x G • fun q : AutQ V => ptN (modelWt U G) (rdU U f) (dict q.out) := rfl
  rw [this, eLpNorm_const_smul, ENNReal.toReal_mul, Real.enorm_eq_ofReal (lieFacZ_pos x G).le,
    ENNReal.toReal_ofReal (lieFacZ_pos x G).le]
  rfl

def bergOn (Z : Comp Xo c) (G : WTZ E) (y : FPt U.X) : ENNReal := bergE V dict (muOn U V dict Z) (modelWt U G) y

theorem homN_sq_le {G : WTZ E} (hμ : μ Set.univ ≤ 1) (hd : ∀ g, (dict g).2 ∈ (U.X (dict g).1).dom) (y : FPt U.X)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : bergE V dict μ (modelWt U G) y ≤ ENNReal.ofReal B) {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (modelWt U G)) :
    homN U x G f ⟨y.1, y.2.1⟩ ^ 2 ≤ B * petAt U x V dict μ G f ^ 2 := by
  have hfin := petE_ne_top V dict μ hμ hd hf
  have h := (bergE_le_iff V dict μ (fun P hP => petE_ne_top V dict μ hμ hd hP) y ENNReal.ofReal_ne_top).1 hB _ hf
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hfin)) h
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (ptN_nonneg _ _ _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0,
    ENNReal.toReal_pow] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (lieFacZ Dw x G))
  unfold homN petAt
  nlinarith [h3]

end One

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7}

theorem petAt_wtZ {σ : c.F →+* ℂ} (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)
    (hm : MuUnit V dict mu) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : JMemL2 V σ (rdC U σ a n) dict mu) {f : Rul Xo c}
    (hf : f ∈ cusp Xo c U a n) : petAt (U σ) x V dict (muQ1 V) (wtZ a n) f = l2C U σ V dict mu x a n h f := by
  rw [l2C, dif_pos hf, petAt, lieFacZ_wtZ]
  congr 1
  show _ = ‖(h ⟨f, hf⟩).toLp _‖
  rw [Lp.norm_toLp, petE]
  congr 1
  refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), ptN, pnorm_eq_of_unit _ _ _ _ (hm.2.2.2 _)]
  show _ = ‖mu q.out * rdU (U σ) f (dict q.out).1 (dict q.out).2‖
  rw [norm_mul, hm.2.1, one_mul]

variable (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def petW (G : WTZ E) (σ : c.F →+* ℂ) (f : Rul Xo c) : ℝ :=
  petAt (U (goodOf c σ)) x (V (goodOf c σ)) (dict (goodOf c σ)) (muQ1 (V (goodOf c σ))) G f

def petOn (Z : Comp Xo c) (G : WTZ E) (σ : c.F →+* ℂ) (f : Rul Xo c) : ℝ :=
  petAt (U (goodOf c σ)) x (V (goodOf c σ)) (dict (goodOf c σ))
    (muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z) G f

theorem petW_smul (G : WTZ E) (σ : c.F →+* ℂ) (a : c.F) (f : Rul Xo c) :
    petW U x V dict G σ (a • f) = ‖σ a‖ * petW U x V dict G σ f := by
  rw [petW, petAt_smul, norm_goodOf]; rfl

theorem petOn_smul (Z : Comp Xo c) (G : WTZ E) (σ : c.F →+* ℂ) (a : c.F) (f : Rul Xo c) :
    petOn U x V dict Z G σ (a • f) = ‖σ a‖ * petOn U x V dict Z G σ f := by
  rw [petOn, petAt_smul, norm_goodOf]; rfl

def normW (G : WTZ E) (σ : c.F →+* ℂ) (f : cuspW Xo c U G) : ℝ := petW U x V dict G σ f

def normOn (Z : Comp Xo c) (G : WTZ E) (σ : c.F →+* ℂ) (f : cuspOn U Z G) : ℝ := petOn U x V dict Z G σ f

def GoodW (G : WTZ E) : Prop :=
  HasGram (normW U x V dict G) ∧ (latW U G).FG ∧ Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⊤

def GoodOn (Z : Comp Xo c) (G : WTZ E) : Prop :=
  HasGram (normOn U x V dict Z G) ∧ (latOn U Z G).FG ∧ Submodule.span c.F (latOn U Z G : Set (cuspOn U Z G)) = ⊤

def rankW (G : WTZ E) : ℕ := Formalism.HN.rkK (latW U G)

def rankOn (Z : Comp Xo c) (G : WTZ E) : ℕ := Formalism.HN.rkK (latOn U Z G)

def slopeW_sq (G : WTZ E) : ℝ := slope_sq (normW U x V dict G) (latW U G)

def slopeOn_sq (Z : Comp Xo c) (G : WTZ E) : ℝ := slope_sq (normOn U x V dict Z G) (latOn U Z G)

def degW (G : WTZ E) : ℝ := deg (normW U x V dict G) (latW U G)

def degOn (Z : Comp Xo c) (G : WTZ E) : ℝ := deg (normOn U x V dict Z G) (latOn U Z G)

def degZ (la : Weight Dw) (m : ℤ) : ℝ := degW U x V dict (wtOf Dw la m)

theorem degW_eq (G : WTZ E) : degW U x V dict G = (rankW U G : ℝ) * (slopeW_sq U x V dict G / 2) := rfl

end Norms

end GlobalTheory.AllWt
