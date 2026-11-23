import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp

noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AllWt (secZ Weight exOf Psi)

section PullLB

variable {Z Z' : Scheme.{0}} {S : Type} [CommRing S] (L : LB Z) (f : Z' ⟶ Z)

theorem le_pull_chart {w : Sp S ⟶ Z'} {j : PUnit → L.ι} (hz : ⊤ ≤ (w ≫ f) ⁻¹ᵁ L.U (j PUnit.unit)) :
    ⊤ ≤ w ⁻¹ᵁ (L.pull f).U j := fun p hp => mem_pull.2 (hz hp)

theorem ev_pull_g (j j' : PUnit → L.ι) (w : Sp S ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ ((L.pull f).U j ⊓ (L.pull f).U j'))
    (hh : ⊤ ≤ (w ≫ f) ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) :
    ev w _ hw ((L.pull f).g j j').val = ev (w ≫ f) _ hh (L.g (j PUnit.unit) (j' PUnit.unit)).val := by
  have hg : (L.pull f).g j j' =
      res (show (L.pull f).U j ⊓ (L.pull f).U j' ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) from
        fun p hp => ⟨mem_pull.1 hp.1, mem_pull.1 hp.2⟩) (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
    show ∏ _k : PUnit.{1}, _ ^ (1 : ℤ) = _
    rw [Fintype.prod_unique]
    exact zpow_one _
  rw [hg]
  exact ev_appLE w f _ hw hh _

variable {L} in

def secPull (s : L.Sec) : (L.pull f).Sec where
  f j := (f.appLE (L.U (j PUnit.unit)) _ (fun _ hp => mem_pull.1 hp)).hom (s.f (j PUnit.unit))
  compat j j' := ext_ev fun S _ w hw => by
    have hh : ⊤ ≤ (w ≫ f) ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun p hp => ⟨(mem_pull (F := f)).1 (hw hp).1, (mem_pull (F := f)).1 (hw hp).2⟩
    have h := congrArg (ev (w ≫ f) _ hh) (s.compat (j PUnit.unit) (j' PUnit.unit))
    have a := le_preimage_mono inf_le_left hh
    have b := le_preimage_mono inf_le_right hh
    rw [map_mul, ev_res _ _ hh a, ev_res _ _ hh b] at h
    rw [map_mul, ev_res w _ hw (le_pull_chart L f a), ev_res w _ hw (le_pull_chart L f b)]
    exact ((ev_appLE w f _ _ a _).trans h).trans
      (congrArg₂ (· * ·) (ev_pull_g L f j j' w hw hh).symm (ev_appLE w f _ _ b _).symm)

end PullLB

section Tri

variable {R : Type} [CommRing R] {m : ℕ} {N : Type} [AddCommGroup N] [Module R N]

theorem exists_tri_of_le {v v' : Fin m → N} (h : ∀ i, initSpan R v' i ≤ initSpan R v i) :
    ∃ b : Matrix (Fin m) (Fin m) R, b.BlockTriangular id ∧ ∀ i, v' i = ∑ j, b j i • v j := by
  have ex : ∀ i : Fin m, ∃ a : Fin m → R, (∀ j : Fin m, (i : ℕ) + 1 ≤ j → a j = 0) ∧ ∑ j, a j • v j = v' i :=
    fun i => mem_initSpan.1 (h _ (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩))
  choose a ha ha' using ex
  exact ⟨fun j i => a i j, fun j i hj => ha i j hj, fun i => (ha' i).symm⟩

theorem exists_tri_of_eq {v v' : Fin m → N} (hv : LinearIndependent R v) (h : ∀ i, initSpan R v' i = initSpan R v i) :
    ∃ b : Matrix (Fin m) (Fin m) R, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ ∀ i, v' i = ∑ j, b j i • v j := by
  obtain ⟨b, hb, e⟩ := exists_tri_of_le fun i => (h i).le
  obtain ⟨b', hb', e'⟩ := exists_tri_of_le fun i => (h i).ge
  refine ⟨b, hb, fun i => IsUnit.of_mul_eq_one (b' i i) ?_, e⟩
  have h1 := e' i
  simp only [e, Finset.smul_sum, smul_smul] at h1
  rw [Finset.sum_comm] at h1
  simp only [← Finset.sum_smul] at h1
  have h2 := (Fintype.linearIndependent_iffₛ.1 hv) (fun j => (1 : Matrix (Fin m) (Fin m) R) j i)
    (fun j => ∑ k, b' k i * b j k) (by rw [← h1]; simp [Matrix.one_apply]) i
  rw [← tri_mul_diag hb hb', Matrix.mul_apply]
  simp only [Matrix.one_apply_eq] at h2
  rw [h2]
  exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _

theorem linearIndependent_of_tri {v v' : Fin m → N} (hv : LinearIndependent R v) {b : Matrix (Fin m) (Fin m) R}
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) (e : ∀ i, v' i = ∑ j, b j i • v j) :
    LinearIndependent R v' := by
  have hd : IsUnit b.det := by
    rw [Matrix.det_of_upperTriangular hb]
    exact IsUnit.prod_univ_iff.2 hu
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro a ha
  simp only [e, Finset.smul_sum, smul_smul] at ha
  rw [Finset.sum_comm] at ha
  simp only [← Finset.sum_smul] at ha
  have h1 : b.mulVec a = 0 := funext fun j => (Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _).trans (hv _ ha j)
  have := congrArg b⁻¹.mulVec h1
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul b hd, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact congrFun this

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem frBor_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

theorem exists_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) : ∃ z, FrMap φ y z := (evLaws_genFr_atlas E H Dw l Xo c).1.bc S T φ y

theorem frMap_refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : FrMap (AlgHom.id c.F S) y y :=
  (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y).2.1

theorem frMap_unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y z') : z = z' :=
  (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S T φ y).1 z z' h h'

theorem spMap_algId {S : Type} [CommRing S] [Algebra c.F S] {Z : Scheme.{0}} (z : Sp S ⟶ Z) :
    spMap (AlgHom.id c.F S).toRingHom ≫ z = z := (congrArg (· ≫ z) (Spec.map_id _)).trans (Category.id_comp _)

theorem spMap_algComp {S S' S'' : Type} [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] [CommRing S'']
    [Algebra c.F S''] (ψ : S →ₐ[c.F] S') (χ : S' →ₐ[c.F] S'') {Z : Scheme.{0}} (z : Sp S ⟶ Z) :
    spMap (χ.comp ψ).toRingHom ≫ z = spMap χ.toRingHom ≫ spMap ψ.toRingHom ≫ z := by
  rw [← Category.assoc, spMap_comp']; rfl

namespace Frames

variable {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {S S' : Type} [CommRing S] [Algebra c.F S] [CommRing S']
  [Algebra c.F S']

def Lies (z : Sp S ⟶ Z) (P : FrPt Xo c S) : Prop :=
  z ≫ π = frX P ≫ Y.j ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (P' : FrPt Xo c S'),
    FrMap ψ P P' → ∀ (k : F.J) (z' : Sp S' ⟶ Z) (_ : spMap ψ.toRingHom ≫ z = z') (hz : ⊤ ≤ z' ⁻¹ᵁ F.U k)
      (hx : z' ≫ π = frX P' ≫ Y.j) (σ : E →+* ℂ) (i : ℕ),
      initSpan S' (frVec Y P' rfl σ) i = initSpan S' (F.vecAt k z' hz hx σ) i

def TopEigen : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : Sp S ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) →
    ∀ (z : Sp S ⟶ Z) (hx : z ≫ π = y ≫ Y.j) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (σ : E →+* ℂ),
      initSpan S (F.vecAt k z hz hx σ) (Dw.mult σ) = eigLie c (y ≫ Y.j) σ

def ChartFr (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (Q : FrPt Xo c S) : Prop :=
  (F.M k).toMChart.Comparison₂ (ev (z ≫ π) (F.M k).U (F.inM hz rfl)) (F.uAt k z hz) Q

variable {F}

theorem ChartFr.over {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q : FrPt Xo c S} (h : F.ChartFr k z hz Q) :
    frX Q ≫ Y.j = z ≫ π := by
  obtain ⟨Λ, -⟩ := h
  rw [← eq_frX Q Λ.xF_fst Λ.xF_snd, Λ.xF_j, spMap_ev]

theorem ChartFr.frVec_eq {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q : FrPt Xo c S} (h : F.ChartFr k z hz Q)
    {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hQ : frX Q ≫ Y.j = x) (σ : E →+* ℂ) :
    frVec Y Q hQ σ = F.vecAt k z hz hx σ := by
  subst hx
  obtain ⟨Λ, h1, -⟩ := h
  exact funext fun i => (vec_iff_toModel _ Λ (eq_frX Q Λ.xF_fst Λ.xF_snd) (frX_fst Q) hQ _ (Q.tan σ i)).1 (h1 σ i)

theorem ChartFr.unique {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q Q' : FrPt Xo c S} (h : F.ChartFr k z hz Q)
    (h' : F.ChartFr k z hz Q') : Q = Q' := frPt_eq_of_tie _ h h'

theorem ChartFr.frMap {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q : FrPt Xo c S} (h : F.ChartFr k z hz Q)
    {ψ : S →ₐ[c.F] S'} {Q' : FrPt Xo c S'} (hQ : FrMap ψ Q Q') {z' : Sp S' ⟶ Z} (ez : spMap ψ.toRingHom ≫ z = z')
    (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k) : F.ChartFr k z' hz' Q' := by
  subst ez
  have := MChart.tie_baseChange E H Dw l Xo c O β Y _ S S' _ ψ _ Q Q' h hQ
  unfold ChartFr
  rw [ev_congr (Category.assoc _ _ _) _ _ (le_preimage_comp _ (F.inM hz rfl)), ev_spMap _ _ _ (F.inM hz rfl),
    funext (F.uAt_spMap k _ z hz hz')]
  exact this

theorem ChartFr.frBor {k k' : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {hz' : ⊤ ≤ z ⁻¹ᵁ F.U k'}
    {Q Q' : FrPt Xo c S} (h : F.ChartFr k z hz Q) (h' : F.ChartFr k' z hz' Q') (hh : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) :
    FrBor (F.TAt k k' z hh) Q Q' := by
  refine frBor_of_frVec (F.inM hz rfl) h.over h'.over _ (fun σ => (F.B k k' σ).map (ev z _ hh))
    (fun σ => F.B_map_tri k k' σ _) (fun σ i => rfl) (fun σ i => ?_) (fun e i => ?_)
  · rw [h.frVec_eq rfl, h'.frVec_eq rfl]
    exact F.vecAt_eq_sum k k' z hz hz' hh rfl σ i
  · obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := Q'
    dsimp only at e
    subst e
    obtain ⟨Λ, -, hs⟩ := h
    obtain ⟨Λ', -, hs'⟩ := h'
    have hM := le_preimage_inf (F.inM hz rfl) (F.inM hz' rfl)
    exact (thTie_change _ _ _ _ hM Λ Λ' hs hs' i).trans
      (congrArg (fun a => scal Q.x a i * Q.s.f i) (F.ev_T_none k k' z hh rfl hM).symm)

theorem TopEigen.exists_chartFr (hT : F.TopEigen) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) {z : Sp S ⟶ Z} (hx : z ≫ π = y ≫ Y.j) (k : F.J)
    (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) : ∃ Q : FrPt Xo c S, F.ChartFr k z hz Q := by
  obtain ⟨Λ⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y (F.M k).toMChart S _ y hy
    (hx.symm.trans (spMap_ev (z ≫ π) (F.M k).hU (F.inM hz rfl)).symm)
  have hE : ∀ σ cv, (F.M k).toMChart.Eig (ev (z ≫ π) (F.M k).U (F.inM hz rfl)) σ cv ↔
      ∃ a : Fin (Dw.mult σ) → S, (F.uAt k z hz σ).mulVec a = cv := fun σ cv => by
    rw [ev_congr hx _ _ (F.inM hz hx), ← vec_mem_eigLie, ← hT S y hy z hx k hz σ, mem_initSpan]
    simp only [sum_vecAt, (vec _ _ _).injective.eq_iff]
    exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, fun j hj => absurd j.2 (not_lt.2 hj), h⟩⟩
  obtain ⟨Q, -, hQ⟩ := exists_frPt_tie GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c O β Y _ S _ _ Λ
    (F.uAt k z hz) (fun σ i => (hE σ _).2 ⟨Pi.single i 1, by rw [Matrix.mulVec_single_one]; rfl⟩)
    (fun σ cv h => by
      obtain ⟨a, ha⟩ := (hE σ cv).1 h
      obtain ⟨w, hw⟩ := F.uAt_split k z hz σ
      refine ⟨a, ha, fun b hb => ?_⟩
      have := congrArg w.mulVec (hb.trans ha.symm)
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hw, Matrix.one_mulVec, Matrix.one_mulVec] at this)
  exact ⟨Q, hQ⟩

theorem Lies.frMap {z : Sp S ⟶ Z} {P : FrPt Xo c S} (h : F.Lies z P) {ψ : S →ₐ[c.F] S'} {P' : FrPt Xo c S'}
    (hP : FrMap ψ P P') : F.Lies (spMap ψ.toRingHom ≫ z) P' :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, frX_frMap hP], fun S'' _ _ χ P'' hP' k z' ez =>
    h.2 S'' (χ.comp ψ) P'' (PullbackSections.frMap_trans ψ χ hP hP') k z' ((spMap_algComp ψ χ z).trans ez)⟩

theorem Lies.frBor {z : Sp S ⟶ Z} {P P₁ : FrPt Xo c S} (h : F.Lies z P) {t : Ix Dw → Sˣ} (hB : FrBor t P P₁) :
    F.Lies z P₁ := by
  refine ⟨by rw [h.1, frX_frBor hB], fun S' _ _ ψ P₁' hP₁ k z' ez hz hx σ i => ?_⟩
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  have hB' := frBor_baseChange ψ hB hP hP₁
  have hB'' := (BorelGroupoid.frBor_groupoid E H Dw l Xo c S').2.2.1 _ _ _ hB'
  have eX : frX P' ≫ Y.j = frX P₁' ≫ Y.j := by rw [frX_frBor hB']
  have key : ∀ (x : Sp S' ⟶ Y.X) (e : frX P' ≫ Y.j = x) (hx' : z' ≫ π = x),
      initSpan S' (frVec Y P' e σ) i = initSpan S' (F.vecAt k z' hz hx' σ) i := by
    rintro _ rfl hx'
    exact h.2 S' ψ P' hP k z' ez hz hx' σ i
  rw [← key _ eX hx]
  obtain ⟨b, hb, -, e⟩ := frVec_of_frBor (F.inM hz hx) eX rfl hB' σ
  obtain ⟨b', hb', -, e'⟩ := frVec_of_frBor (F.inM hz hx) rfl eX hB'' σ
  exact le_antisymm (initSpan_le_of_tri hb e i) (initSpan_le_of_tri hb' e' i)

theorem ChartFr.lies {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q : FrPt Xo c S} (h : F.ChartFr k z hz Q) :
    F.Lies z Q := by
  refine ⟨h.over.symm, fun S' _ _ ψ Q' hQ k' z' ez hz' hx σ i => ?_⟩
  have hk : ⊤ ≤ z' ⁻¹ᵁ F.U k := ez ▸ le_preimage_comp _ hz
  rw [(h.frMap hQ ez hk).frVec_eq hx rfl, F.initSpan_vecAt_eq k k' z' hk hz']

theorem Lies.initSpan_eq {z : Sp S ⟶ Z} {P : FrPt Xo c S} (h : F.Lies z P) {k : F.J} (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hP : frX P ≫ Y.j = x) (σ : E →+* ℂ) (i : ℕ) :
    initSpan S (frVec Y P hP σ) i = F.step z hx σ i := by
  subst hP
  rw [F.step_eq k z hz]
  exact h.2 S (AlgHom.id c.F S) P (frMap_refl P) k z (spMap_algId z) hz hx σ i

theorem ChartFr.exists_frBor {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q P : FrPt Xo c S}
    (h : F.ChartFr k z hz Q) (hP : F.Lies z P) : ∃ t, FrBor t Q P := by
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y P hP.1.symm σ i = ∑ j, b j i • frVec Y Q h.over σ j := fun σ => by
    rw [h.frVec_eq rfl]
    exact exists_tri_of_eq (F.linearIndependent_vecAt k z hz rfl σ) fun i =>
      (hP.initSpan_eq hz rfl _ σ i).trans (F.step_eq k z hz rfl σ i)
  choose b hb hu hv using ex
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) (hP.1.symm.trans h.over.symm)]
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
  dsimp only at e
  subst e
  obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
  exact ⟨_, frBor_of_frVec (F.inM hz rfl) h.over hP.1.symm
    (fun ix => match ix with | none => u0 | some p => (hu p.1 p.2).unit) b hb (fun _ _ => rfl) hv fun _ => hu0⟩

theorem TopEigen.mem_step_top_iff (hT : F.TopEigen) {V K : Type} [CommRing V] [IsLocalRing V] [CommRing K]
    [Algebra c.F K] (φ : V →+* K) (hφ : Function.Injective φ) (z : Sp V ⟶ Z) {x : Sp V ⟶ Y.X} (hx : z ≫ π = x)
    {y : Sp K ⟶ Xo.XF c} (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F K)) (e : spMap φ ≫ x = y ≫ Y.j)
    (σ : E →+* ℂ) (v : TanM x Y.t.G) :
    v ∈ F.step z hx σ (Dw.mult σ) ↔ tanPull φ e v ∈ eigLie c (y ≫ Y.j) σ := by
  have hxK : (spMap φ ≫ z) ≫ π = y ≫ Y.j := by rw [Category.assoc, hx, e]
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing F.cover z
  rw [F.mem_step_iff_of_injective φ hφ z hx rfl hxK e, F.step_eq k _ (le_preimage_comp _ hz), hT K y hy]

theorem TopEigen.diag_unit (hT : F.TopEigen) {V K : Type} [CommRing V] [IsLocalRing V] [CommRing K]
    [Algebra c.F K] (φ : V →+* K) (hφ : Function.Injective φ) (z : Sp V ⟶ Z) {k : F.J} (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    {P Q : FrPt Xo c K} (hP : F.Lies (spMap φ ≫ z) P) (e : spMap φ ≫ z ≫ π = frX P ≫ Y.j) (σ : E →+* ℂ)
    (ub : Fin (Dw.mult σ) → TanM (z ≫ π) Y.t.G) (hub : ∀ i, tanPull φ e (ub i) = frVec Y P rfl σ i)
    (hsp : ∀ v, tanPull φ e v ∈ eigLie c (frX P ≫ Y.j) σ → ∃ a : Fin (Dw.mult σ) → V, ∑ i, a i • ub i = v)
    (hQ : F.ChartFr k (spMap φ ≫ z) (le_preimage_comp _ hz) Q) {t : Ix Dw → Kˣ} (ht : FrBor t Q P) :
    (∀ i, initSpan V ub i = F.step z rfl σ i) ∧ ∀ i, ∃ u : Vˣ, φ u = t (some ⟨σ, i⟩) := by
  have hz' := le_preimage_comp (spMap φ) hz
  have hx : (spMap φ ≫ z) ≫ π = frX P ≫ Y.j := hP.1
  obtain ⟨b', hb', hd', e'⟩ := frVec_of_frBor (F.inM hz' hx) (hQ.over.trans hx) rfl ht σ
  rw [hQ.frVec_eq hx] at e'
  have hK := F.linearIndependent_vecAt k _ hz' hx σ
  have hli := linearIndependent_of_tri hK hb' (fun i => by rw [hd']; exact Units.isUnit _) e'
  have h1 : ∀ i, initSpan V ub i = F.step z rfl σ i := fun i => by
    refine le_antisymm (Submodule.span_le.2 ?_) fun v hv => ?_
    · rintro _ ⟨j, hj, rfl⟩
      refine (F.mem_step_iff_of_injective φ hφ z rfl rfl hx e σ i _).2 ?_
      rw [hub, ← hP.initSpan_eq hz' hx rfl]
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    · have h2 := F.tanPull_mem_step φ z rfl rfl hx e σ i hv
      obtain ⟨a, rfl⟩ := hsp v (by
        rw [← hT K _ (frX_snd P) _ hx k hz']
        rw [F.step_eq k _ hz'] at h2
        obtain ⟨d, -, hd⟩ := mem_initSpan.1 h2
        exact mem_initSpan.2 ⟨d, fun j hj => absurd j.2 (not_lt.2 hj), hd⟩)
      rw [← hP.initSpan_eq hz' hx rfl, map_sum] at h2
      simp only [map_smulₛₗ, hub] at h2
      obtain ⟨d, hd, h3⟩ := mem_initSpan.1 h2
      refine mem_initSpan.2 ⟨a, fun j hj => hφ ?_, rfl⟩
      rw [map_zero, ← hd j hj]
      exact ((Fintype.linearIndependent_iffₛ.1 hli) _ _ h3 j).symm
  refine ⟨h1, fun i => ?_⟩
  obtain ⟨b, -, hu, eb⟩ := exists_tri_of_eq (F.linearIndependent_vecAt k z hz rfl σ)
    fun i => (h1 i).trans (F.step_eq k z hz rfl σ i)
  refine ⟨(hu i).unit, ?_⟩
  have h4 := congrArg (tanPull (G := Y.t.G) φ e) (eb i)
  rw [hub, e', map_sum] at h4
  simp only [map_smulₛₗ, F.tanPull_vecAt k φ z hz hz' rfl hx e] at h4
  rw [← hd']
  exact ((Fintype.linearIndependent_iffₛ.1 hK) _ _ h4 i).symm

def coord (M : GChart Y) (h : ∀ σ, Dw.mult σ ≤ M.n) : Frames Y M.U.ι where
  J := Unit
  U _ := ⊤
  cover := iSup_const
  M _ := M
  le _ := fun p _ => p.2
  u _ σ := (1 : Matrix _ _ _).submatrix id (Fin.castLE (h σ))
  split _ σ := ⟨(1 : Matrix _ _ _).submatrix (Fin.castLE (h σ)) id, by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.one_mul,
      Matrix.submatrix_one _ (Fin.castLE_injective _)]⟩
  tri _ _ σ := ⟨1, Matrix.blockTriangular_one, by
    have e : chg M.toMChart M.toMChart = 1 := Module.Basis.toMatrix_self _
    rw [e, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Matrix.one_mul _).trans (Matrix.mul_one _).symm⟩

example (M : GChart Y) (h : ∀ σ, Dw.mult σ ≤ M.n) (z : Sp S ⟶ M.U.toScheme) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    (coord M h).vecAt () z le_top rfl σ i =
      lieBasis M.toMChart _ ((coord M h).inM (k := ()) le_top rfl) (Fin.castLE (h σ) i) := by
  have hu : ∀ j : Fin M.n, (coord M h).uAt () z le_top σ j i = if j = Fin.castLE (h σ) i then 1 else 0 := fun j => by
    show ev z ⊤ le_top ((1 : Matrix (Fin M.n) (Fin M.n) _) j (Fin.castLE (h σ) i)) = _
    rw [Matrix.one_apply, apply_ite (ev z ⊤ le_top), map_one, map_zero]
  refine (congrArg (vec M.toMChart _ ((coord M h).inM (k := ()) le_top rfl)) (funext hu)).trans ?_
  exact (vec_apply _ _ _ _).trans (by simp)

open Classical in

theorem LL_single_one (F : Frames Y π) (ix : Ix Dw) : F.LL (Pi.single ix 1) = GlobalTheory.CechPic.dual (F.line ix) := by
  unfold LL line GlobalTheory.CechPic.dual
  congr 1
  funext k k'
  rw [Finset.prod_eq_single ix (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp) (by simp)]
  simp

end Frames

section Weights

theorem mult_of_mem (τ : Psi H) : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]

theorem mult_conj (τ : Psi H) : Dw.mult (conjEmb τ.1) = Dw.q := by simp [Datum.mult, GlobalTheory.AllWt.conj_not_mem τ]

theorem exOf_none (la : Weight Dw) : exOf Dw la 0 none = 0 := rfl

theorem exOf_big (la : Weight Dw) (τ : Psi H) (i : Fin (Dw.mult τ.1)) :
    exOf Dw la 0 (some ⟨τ.1, i⟩) = la τ ⟨i, by have := i.2; have := mult_of_mem (Dw := Dw) τ; omega⟩ :=
  (GlobalTheory.AllWt.wtOf_big la 0 τ i (mult_of_mem (Dw := Dw) τ ▸ i.2)).trans (sub_zero _)

theorem exOf_small (la : Weight Dw) (τ : Psi H) (i : Fin (Dw.mult (conjEmb τ.1))) :
    exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) =
      -la τ ⟨Dw.p + (Dw.q - 1 - i), by have := i.2; have := mult_conj (Dw := Dw) τ; omega⟩ :=
  (GlobalTheory.AllWt.wtOf_small la 0 τ i (mult_conj (Dw := Dw) τ ▸ i.2)).trans (sub_zero _)

theorem exOf_ext {la : Weight Dw} {e : Ix Dw → ℤ} (h0 : e none = 0)
    (h1 : ∀ (τ : Psi H) (i : Fin (Dw.mult τ.1)) hi, la τ ⟨i, hi⟩ = e (some ⟨τ.1, i⟩))
    (h2 : ∀ (τ : Psi H) (i : Fin (Dw.mult (conjEmb τ.1))) hi,
      -la τ ⟨Dw.p + (Dw.q - 1 - i), hi⟩ = e (some ⟨conjEmb τ.1, i⟩)) : exOf Dw la 0 = e := by
  funext ix
  rcases ix with _ | ⟨σ, i⟩
  · exact h0.symm
  · by_cases h : σ (H.rt : E) = H.rt0
    · exact (exOf_big la ⟨σ, h⟩ i).trans (h1 ⟨σ, h⟩ i _)
    · obtain ⟨τ, rfl⟩ : ∃ τ : Psi H, σ = conjEmb τ.1 :=
        ⟨⟨conjEmb σ, GlobalTheory.AllWt.conj_mem h⟩, (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm⟩
      exact (exOf_small la τ i).trans (h2 τ i _)

variable (Dw) in

def mu0 : Weight Dw := fun _ i => if (i : ℕ) < Dw.p then 1 else -1

theorem unitaryWeightExponentVector_signatureWeightMuZero : exOf Dw (mu0 Dw) 0 = fun ix => ix.elim 0 fun _ => 1 :=
  exOf_ext rfl (fun τ i _ => if_pos (i.2.trans_eq (mult_of_mem τ)))
    fun τ i _ => by simp [mu0]

end Weights

def genMap {Z : Scheme.{0}} (π : Z ⟶ Y.X) : pullback (π ≫ Y.s) (spMap β) ⟶ pullback Y.s (spMap β) :=
  pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])

structure FlagCover (Y : Model Xo c β) where
  YY : Scheme.{0}
  π : YY ⟶ Y.X
  proper : IsProper π
  normal : Geo.Tor.IsNormalScheme YY
  flat : Flat (π ≫ Y.s)
  F : Frames Y π
  dense : Dense (genMap π ⁻¹' Set.range Y.jQ)
  top : F.TopEigen
  rep : ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S), ∃! z : Sp S ⟶ YY, F.Lies z P

structure FlagModel (Y : Model Xo c β) extends FlagCover Y where
  fin : ∀ (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ YY),
    {z' : Sp K ⟶ YY | ∃ hx : z' ≫ π = z ≫ π, ∀ σ i, F.step z' hx σ i = F.step z rfl σ i}.Finite

namespace FlagCover

variable (X : FlagCover Y) {S S' : Type} [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S']

abbrev Yo : Scheme.{0} := pullback X.π Y.j

abbrev inc : X.Yo ⟶ X.YY := pullback.fst X.π Y.j

abbrev gr (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : LB X.YY := X.F.gr σ i

abbrev LL (e : Ix Dw → ℤ) : LB X.YY := X.F.LL e

abbrev de : LB X.YY := X.F.de

abbrev detOm : LB X.YY := X.F.detOm

def Llam (la : Weight Dw) : LB X.YY := X.F.LL (exOf Dw la 0)

theorem isLB_Llam (la : Weight Dw) : (X.Llam la).IsLB := X.F.isLB_LL _

def ptY (P : FrPt Xo c S) : Sp S ⟶ X.YY := (X.rep S P).exists.choose

theorem lies_ptY (P : FrPt Xo c S) : X.F.Lies (X.ptY P) P := (X.rep S P).exists.choose_spec

variable {X} in
theorem eq_ptY {P : FrPt Xo c S} {z : Sp S ⟶ X.YY} (h : X.F.Lies z P) : z = X.ptY P :=
  (X.rep S P).unique h (X.lies_ptY P)

def pt (P : FrPt Xo c S) : Sp S ⟶ X.Yo := pullback.lift (X.ptY P) (frX P) (X.lies_ptY P).1

theorem pt_inc (P : FrPt Xo c S) : X.pt P ≫ X.inc = X.ptY P := pullback.lift_fst _ _ _

theorem pt_snd (P : FrPt Xo c S) : X.pt P ≫ pullback.snd _ _ = frX P := pullback.lift_snd _ _ _

theorem ptY_frMap {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P') :
    spMap ψ.toRingHom ≫ X.ptY P = X.ptY P' := eq_ptY ((X.lies_ptY P).frMap h)

theorem pt_frMap {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P') :
    spMap ψ.toRingHom ≫ X.pt P = X.pt P' :=
  pullback.hom_ext (by rw [Category.assoc, pt_inc, pt_inc, X.ptY_frMap h])
    (by rw [Category.assoc, pt_snd, pt_snd, frX_frMap h])

theorem ptY_frBor {t : Ix Dw → Sˣ} {P P' : FrPt Xo c S} (h : FrBor t P P') : X.ptY P = X.ptY P' :=
  eq_ptY ((X.lies_ptY P).frBor h)

theorem pt_frBor {t : Ix Dw → Sˣ} {P P' : FrPt Xo c S} (h : FrBor t P P') : X.pt P = X.pt P' :=
  pullback.hom_ext (by rw [pt_inc, pt_inc, X.ptY_frBor h]) (by rw [pt_snd, pt_snd, frX_frBor h])

theorem exists_chartFr (w : Sp S ⟶ X.Yo) (hw : w ≫ pullback.snd _ _ ≫ pullback.snd _ _ = spMap (algebraMap c.F S))
    (k : X.F.J) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    ∃ Q : FrPt Xo c S, X.F.ChartFr k (w ≫ X.inc) hz Q ∧ X.pt Q = w := by
  have hx : (w ≫ X.inc) ≫ X.π = (w ≫ pullback.snd _ _) ≫ Y.j := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hy : (w ≫ pullback.snd _ _) ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by rw [Category.assoc, hw]
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hx k hz
  exact ⟨Q, hQ, pullback.hom_ext (by rw [pt_inc, ← eq_ptY hQ.lies])
    (by rw [pt_snd]; exact xF_ext (Y := Y) (frX_snd Q) hy (hQ.over.trans hx))⟩

theorem points [IsLocalRing S] :
    (∀ w : Sp S ⟶ X.Yo, w ≫ pullback.snd _ _ ≫ pullback.snd _ _ = spMap (algebraMap c.F S) ↔ ∃ P, X.pt P = w) ∧
      ∀ P P' : FrPt Xo c S, X.pt P = X.pt P' ↔ ∃ t, FrBor t P P' := by
  refine ⟨fun w => ⟨fun hw => ?_, ?_⟩, fun P P' => ⟨fun e => ?_, fun ⟨t, h⟩ => X.pt_frBor h⟩⟩
  · obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing X.F.cover (w ≫ X.inc)
    exact (X.exists_chartFr w hw k hz).imp fun _ h => h.2
  · rintro ⟨P, rfl⟩
    rw [← Category.assoc, pt_snd, frX_snd]
  · have e' : X.ptY P = X.ptY P' := by rw [← pt_inc, e, pt_inc]
    obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing X.F.cover (X.ptY P)
    obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (frX_snd P) (X.lies_ptY P).1 k hz
    obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY P)
    obtain ⟨t', ht'⟩ := hQ.exists_frBor (e' ▸ X.lies_ptY P')
    obtain ⟨-, g1, g2, -⟩ := BorelGroupoid.frBor_groupoid E H Dw l Xo c S
    exact ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩

abbrev SecO (e : Ix Dw → ℤ) : Type := ((X.F.LL e).pull X.inc).Sec

variable {X} {e : Ix Dw → ℤ}

omit [Algebra c.F S] in
theorem le_pull {w : Sp S ⟶ X.Yo} {k : X.F.J} (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    ⊤ ≤ w ⁻¹ᵁ ((X.F.LL e).pull X.inc).U (fun _ => k) := fun p hp => mem_pull.2 (hz hp)

def coef (s : X.SecO e) (k : X.F.J) (w : Sp S ⟶ X.Yo) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) : S :=
  ev w _ (le_pull hz) (s.f fun _ => k)

def resO (s : (X.F.LL e).Sec) : X.SecO e := secPull X.inc s

omit [Algebra c.F S] in
theorem coef_resO (s : (X.F.LL e).Sec) (k : X.F.J) (w : Sp S ⟶ X.Yo) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    coef (resO s) k w hz = ev (w ≫ X.inc) (X.F.U k) hz (s.f k) := ev_appLE w X.inc _ _ hz _

omit [Algebra c.F S] in
open Classical in
theorem coef_change (s : X.SecO e) (k k' : X.F.J) (w : Sp S ⟶ X.Yo) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k)
    (hz' : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k') (hh : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    coef s k w hz = (∏ ix, X.F.TAt k k' (w ≫ X.inc) hh ix ^ (-e ix)).val * coef s k' w hz' := by
  have hw := le_preimage_inf (le_pull (e := e) hz) (le_pull (e := e) hz')
  have h := congrArg (ev w _ hw) (s.compat (fun _ => k) (fun _ => k'))
  rw [map_mul] at h
  refine (ev_res w _ hw _ _).symm.trans (h.trans (congrArg₂ (· * ·) ?_ (ev_res w _ hw _ _)))
  rw [← X.F.ev_LL_g e k k' _ hh]
  exact ev_pull_g (X.F.LL e) X.inc (fun _ => k) (fun _ => k') w hw hh

omit [Algebra c.F S] [Algebra c.F S'] in
theorem coef_spMap (s : X.SecO e) (k : X.F.J) (φ : S →+* S') (w : Sp S ⟶ X.Yo) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k)
    {w' : Sp S' ⟶ X.Yo} (ew : spMap φ ≫ w = w') (hz' : ⊤ ≤ (w' ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    coef s k w' hz' = φ (coef s k w hz) := by
  subst ew
  rw [coef, ev_spMap φ w _ (le_pull hz)]
  rfl

open Classical in

def IsValAt (s : X.SecO e) (P : FrPt Xo c S) (a : S) : Prop :=
  ∀ (k : X.F.J) (hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c S) (t : Ix Dw → Sˣ),
    X.F.ChartFr k (X.pt P ≫ X.inc) hz Q → FrBor t Q P → a = (∏ ix, t ix ^ e ix).val * coef s k (X.pt P) hz

def IsVal (s : X.SecO e) (P : FrPt Xo c S) (a : S) : Prop :=
  ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (P' : FrPt Xo c S'), FrMap ψ P P' →
    IsValAt s P' (ψ a)

variable (X) in
theorem exists_chartFr_frBor (P : FrPt Xo c S) (k : X.F.J) (hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    ∃ (Q : FrPt Xo c S) (t : Ix Dw → Sˣ), X.F.ChartFr k (X.pt P ≫ X.inc) hz Q ∧ FrBor t Q P := by
  have hl : X.F.Lies (X.pt P ≫ X.inc) P := by rw [pt_inc]; exact X.lies_ptY P
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (frX_snd P) hl.1 k hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  exact ⟨Q, t, hQ, ht⟩

open Classical in

theorem isValAt_of_chart (s : X.SecO e) {P Q : FrPt Xo c S} {k : X.F.J} {hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k}
    {t : Ix Dw → Sˣ} (hQ : X.F.ChartFr k (X.pt P ≫ X.inc) hz Q) (ht : FrBor t Q P) :
    IsValAt s P ((∏ ix, t ix ^ e ix).val * coef s k (X.pt P) hz) := by
  intro k' hz' Q' t' hQ' ht'
  obtain ⟨-, g1, -, g3⟩ := BorelGroupoid.frBor_groupoid E H Dw l Xo c S
  have hh := le_preimage_inf hz hz'
  rw [g3 _ _ _ _ ht (g1 _ _ _ _ _ (hQ.frBor hQ' hh) ht'), coef_change s k k' _ hz hz' hh, ← _root_.mul_assoc,
    ← Units.val_mul, ← Finset.prod_mul_distrib]
  congr 2
  exact Finset.prod_congr rfl fun ix _ => by
    rw [Pi.mul_apply, mul_zpow, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, _root_.one_mul]

theorem existsUnique_isValAt (s : X.SecO e) (P : FrPt Xo c S) (k : X.F.J) (hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    ∃! a, IsValAt s P a := by
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor P k hz
  exact ⟨_, isValAt_of_chart s hQ ht, fun a ha => ha k hz Q t hQ ht⟩

theorem IsValAt.frMap {s : X.SecO e} {P : FrPt Xo c S} {a : S} (h : IsValAt s P a) {k : X.F.J}
    (hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k) {ψ : S →ₐ[c.F] S'} {P' : FrPt Xo c S'} (hP : FrMap ψ P P') :
    IsValAt s P' (ψ a) := by
  classical
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor P k hz
  obtain ⟨Q', hQQ⟩ := exists_frMap ψ Q
  have ez : spMap ψ.toRingHom ≫ X.pt P ≫ X.inc = X.pt P' ≫ X.inc := by rw [← Category.assoc, X.pt_frMap hP]
  have hz' : ⊤ ≤ (X.pt P' ≫ X.inc) ⁻¹ᵁ X.F.U k := ez ▸ le_preimage_comp _ hz
  have := isValAt_of_chart s (hQ.frMap hQQ ez hz') (frBor_baseChange ψ ht hQQ hP)
  convert this using 1
  rw [h k hz Q t hQ ht, map_mul, coef_spMap s k ψ.toRingHom _ hz (X.pt_frMap hP) hz']
  congr 1
  show (Units.map (ψ : S →* S') (∏ ix, t ix ^ e ix)).val = _
  simp only [map_prod, map_zpow]

theorem existsUnique_isVal (s : X.SecO e) (P : FrPt Xo c S) : ∃! a, IsVal s P a := by
  have tr : ∀ {S' : Type} [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {P' : FrPt Xo c S'}, FrMap ψ P P' →
      ∀ k, ⊤ ≤ (spMap ψ.toRingHom ≫ X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k ↔ ⊤ ≤ (X.pt P' ≫ X.inc) ⁻¹ᵁ X.F.U k :=
    fun hP k => by rw [← Category.assoc, X.pt_frMap hP]
  have ex : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (k : X.F.J),
      ⊤ ≤ (spMap ψ.toRingHom ≫ X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k → ∃ b : S', ∀ P', FrMap ψ P P' → IsValAt s P' b := by
    intro S' _ _ ψ k h
    obtain ⟨P', hP⟩ := exists_frMap ψ P
    obtain ⟨b, hb, -⟩ := existsUnique_isValAt s P' k ((tr hP k).1 h)
    exact ⟨b, fun P'' hP'' => frMap_unique hP hP'' ▸ hb⟩
  choose val hval using ex
  obtain ⟨a, ha, hu⟩ := glue_val (X.pt P ≫ X.inc) X.F.cover val (fun S' S'' _ _ _ _ ψ χ k k' h h' => by
    obtain ⟨P', hP⟩ := exists_frMap ψ P
    obtain ⟨P'', hP'⟩ := exists_frMap χ P'
    have hP'' := PullbackSections.frMap_trans ψ χ hP hP'
    exact (existsUnique_isValAt s P'' k' ((tr hP'' k').1 h')).unique (hval _ _ k' h' P'' hP'')
      ((hval _ _ k h P' hP).frMap ((tr hP k).1 h) hP'))
  refine ⟨a, fun S' _ _ ψ P' hP k hz => ?_, fun b hb => hu b fun S' _ _ ψ k h => ?_⟩
  · rw [ha S' ψ k ((tr hP k).2 hz)]
    exact hval _ _ k _ P' hP k hz
  · obtain ⟨P', hP⟩ := exists_frMap ψ P
    exact (existsUnique_isValAt s P' k ((tr hP k).1 h)).unique (hb S' ψ P' hP) (hval _ _ k h P' hP)

def val (s : X.SecO e) (P : FrPt Xo c S) : S := (existsUnique_isVal s P).exists.choose

theorem isVal_val (s : X.SecO e) (P : FrPt Xo c S) : IsVal s P (val s P) := (existsUnique_isVal s P).exists.choose_spec

theorem IsVal.eq_val {s : X.SecO e} {P : FrPt Xo c S} {a : S} (h : IsVal s P a) : a = val s P :=
  (existsUnique_isVal s P).unique h (isVal_val s P)

open Classical in

theorem val_eq (s : X.SecO e) {P Q : FrPt Xo c S} {k : X.F.J} {hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k}
    {t : Ix Dw → Sˣ} (hQ : X.F.ChartFr k (X.pt P ≫ X.inc) hz Q) (ht : FrBor t Q P) :
    val s P = (∏ ix, t ix ^ e ix).val * coef s k (X.pt P) hz :=
  isVal_val s P S (AlgHom.id c.F S) P (frMap_refl P) k hz Q t hQ ht

theorem val_chartFr (s : X.SecO e) {Q : FrPt Xo c S} {k : X.F.J} {hz : ⊤ ≤ (X.pt Q ≫ X.inc) ⁻¹ᵁ X.F.U k}
    (hQ : X.F.ChartFr k (X.pt Q ≫ X.inc) hz Q) : val s Q = coef s k (X.pt Q) hz := by
  rw [val_eq s hQ ((BorelGroupoid.frBor_groupoid E H Dw l Xo c S).1 Q)]
  simp

theorem val_frMap (s : X.SecO e) {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P') :
    val s P' = ψ (val s P) :=
  (IsVal.eq_val fun S'' _ _ χ P'' h' => isVal_val s P S'' (χ.comp ψ) P'' (PullbackSections.frMap_trans ψ χ h h')).symm

open Classical in
theorem val_frBor (s : X.SecO e) {t : Ix Dw → Sˣ} {P P₁ : FrPt Xo c S} (h : FrBor t P P₁) :
    val s P₁ = (∏ ix, t ix ^ e ix).val * val s P := by
  refine (IsVal.eq_val fun S' _ _ ψ P₁' h₁ k hz Q t' hQ ht' => ?_).symm
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  have hB := frBor_baseChange ψ h hP h₁
  obtain ⟨-, g1, g2, -⟩ := BorelGroupoid.frBor_groupoid E H Dw l Xo c S'
  have key : ∀ (w : Sp S' ⟶ X.Yo) (_ : X.pt P' = w) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k (w ≫ X.inc) hz Q → ψ (val s P) =
        (∏ ix, (t' * (fun i => Units.map (ψ : S →* S') (t i))⁻¹) ix ^ e ix).val * coef s k w hz := by
    rintro _ rfl hz hQ
    exact isVal_val s P S' ψ P' hP k hz Q _ hQ (g1 _ _ _ _ _ ht' (g2 _ _ _ hB))
  rw [map_mul, key _ (X.pt_frBor hB) hz hQ, ← _root_.mul_assoc]
  congr 1
  show (Units.map (ψ : S →* S') (∏ ix, t ix ^ e ix) * _).val = _
  rw [map_prod, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun ix _ => by
    rw [map_zpow, Pi.mul_apply, Pi.inv_apply, ← mul_zpow, mul_comm (t' ix), mul_inv_cancel_left]

def toRule (s : X.SecO e) : Rul Xo c := fun _ P => val s P

theorem toRule_mem_secZ (s : X.SecO e) : toRule s ∈ secZ Xo c e :=
  ⟨fun _ _ _ _ _ h => val_frMap s h, fun _ _ _ _ h => by
    show val s _ = _ * val s _
    convert val_frBor s h⟩

theorem evR_toRule (s : X.SecO e) (P : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) P) :
    evR Xo c (toRule s) P = val s P := by
  unfold evR evalAt
  rw [dif_pos h]
  exact (val_frMap s h.choose_spec.choose_spec.choose_spec).symm

theorem evR_toRule_of_isReduced [_root_.IsReduced S] (s : X.SecO e) (P : FrPt Xo c S) :
    evR Xo c (toRule s) P = val s P := evR_toRule s P ((evLaws_genFr_atlas E H Dw l Xo c).1.test S P)

theorem val_add {s s₁ s₂ : X.SecO e} (h : ∀ j, s.f j = s₁.f j + s₂.f j) (P : FrPt Xo c S) :
    val s P = val s₁ P + val s₂ P := by
  refine (IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
  rw [map_add, isVal_val s₁ P S' ψ P' hP k hz Q t hQ ht, isVal_val s₂ P S' ψ P' hP k hz Q t hQ ht, ← mul_add]
  exact congrArg _ ((congrArg _ (h _)).trans (map_add _ _ _)).symm

theorem val_mul {e₁ e₂ : Ix Dw → ℤ} {s : X.SecO (e₁ + e₂)} {s₁ : X.SecO e₁} {s₂ : X.SecO e₂}
    (h : ∀ j, s.f j = (show Γ(X.Yo, ((X.F.LL (e₁ + e₂)).pull X.inc).U j) from s₁.f j) *
      (show Γ(X.Yo, ((X.F.LL (e₁ + e₂)).pull X.inc).U j) from s₂.f j)) (P : FrPt Xo c S) :
    val s P = val s₁ P * val s₂ P := by
  refine (IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
  have hc : coef s k (X.pt P') hz = coef s₁ k (X.pt P') hz * coef s₂ k (X.pt P') hz :=
    (congrArg _ (h _)).trans (map_mul _ _ _)
  rw [map_mul, isVal_val s₁ P S' ψ P' hP k hz Q t hQ ht, isVal_val s₂ P S' ψ P' hP k hz Q t hQ ht, hc]
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  ring

theorem eq_of_val_eq {s s' : X.SecO e}
    (h : ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S), val s P = val s' P) : s = s' := by
  refine TieUniq.sec_ext fun j => ext_ev fun S _ w hw => ?_
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
  letI : Algebra c.F S :=
    ((ev (w ≫ pullback.snd X.π Y.j ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  have hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k := fun p hp => mem_pull.1 (hw hp)
  obtain ⟨Q, hQ, ew⟩ := X.exists_chartFr w (spMap_ev_top _).symm k hz
  have key : ∀ (w : Sp S ⟶ X.Yo) (_ : X.pt Q = w) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k (w ≫ X.inc) hz Q → coef s k w hz = coef s' k w hz := by
    rintro _ rfl hz hQ
    exact (val_chartFr s hQ).symm.trans ((h S Q).trans (val_chartFr s' hQ))
  exact key w ew hz hQ

variable (X)

open Classical in

theorem Llam_single_big (τ : Psi H) (i : Fin (Dw.mult τ.1)) (hi : (i : ℕ) < Dw.p + Dw.q) :
    X.Llam (Pi.single τ (Pi.single ⟨i, hi⟩ (-1))) = X.gr τ.1 i := by
  have hp := mult_of_mem (Dw := Dw) τ
  refine (congrArg X.F.LL (exOf_ext (by simp) (fun τ' j hj => ?_) fun τ' j hj => ?_)).trans (X.F.LL_single_neg _)
  · by_cases e : τ' = τ
    · subst e
      simp [Pi.single_apply, Fin.ext_iff]
    · have : τ'.1 ≠ τ.1 := fun h => e (Subtype.ext h)
      simp [Pi.single_apply, e, this]
  · have : conjEmb τ'.1 ≠ τ.1 := fun h => GlobalTheory.AllWt.conj_not_mem τ' (h ▸ τ.2)
    have h2 : Dw.p + (Dw.q - 1 - j) ≠ i := by have := i.2; omega
    by_cases e : τ' = τ
    · subst e
      simp [Pi.single_apply, Fin.ext_iff, this, h2]
    · simp [Pi.single_apply, e, this]

open Classical in

theorem Llam_single_small (τ : Psi H) (i : Fin (Dw.mult (conjEmb τ.1)))
    (hi : Dw.p + (Dw.q - 1 - i) < Dw.p + Dw.q) :
    X.Llam (Pi.single τ (Pi.single ⟨_, hi⟩ (-1))) = GlobalTheory.CechPic.dual (X.gr (conjEmb τ.1) i) := by
  have hq := mult_conj (Dw := Dw) τ
  refine (congrArg X.F.LL (exOf_ext (by simp) (fun τ' j hj => ?_) fun τ' j hj => ?_)).trans (X.F.LL_single_one _)
  · have : τ'.1 ≠ conjEmb τ.1 := fun h => GlobalTheory.AllWt.conj_not_mem τ (h ▸ τ'.2)
    have h2 : (j : ℕ) ≠ Dw.p + (Dw.q - 1 - i) := by have := j.2; have := mult_of_mem (Dw := Dw) τ'; omega
    by_cases e : τ' = τ
    · subst e
      simp [Pi.single_apply, Fin.ext_iff, this, h2]
    · simp [Pi.single_apply, e, this]
  · by_cases e : τ' = τ
    · subst e
      have : Dw.q - 1 - j = Dw.q - 1 - i ↔ (j : ℕ) = i := by have := i.2; have := j.2; omega
      by_cases h : (j : ℕ) = i <;> simp [Pi.single_apply, Fin.ext_iff, this, h]
    · have : conjEmb τ'.1 ≠ conjEmb τ.1 := fun h => e (Subtype.ext (by
        rw [← GlobalTheory.AllWt.conjEmb_conjEmb τ'.1, h, GlobalTheory.AllWt.conjEmb_conjEmb]))
      simp [Pi.single_apply, e, this]

example (k k' : X.F.J) : (X.LL 0).g k k' = 1 := Finset.prod_eq_one fun _ _ => zpow_zero _

end FlagCover

end GlobalTheory.FlagMod
