import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Abstract

variable {K : Type} [Field K] {ιB : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

def MapTransId : Prop :=
  ∀ (S T : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] (φ : S →ₐ[K] T) (y : pts S)
    (z w : pts T), mapR φ y z → mapR (AlgHom.id K T) z w → mapR φ y w

variable {pts mapR}
variable {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ιB → Sˣ) → pts S → pts S → Prop}
variable {G : Type} [Group G] {actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop}

theorem fromTest_of_id (hTr : MapTransId pts mapR) {S : Type} [CommRing S] [Algebra K S] {z w : pts S}
    (h : mapR (AlgHom.id K S) z w) (hz : FromTest pts mapR z) : FromTest pts mapR w := by
  obtain ⟨p, φ, y', hy⟩ := hz
  exact ⟨p, φ, y', hTr _ _ φ y' z w hy h⟩

private theorem evalAt_eq_lemma (hWD : EvalWD pts mapR) {f : Rules pts} (hf : IsNatural pts mapR f) {S : Type}
    [CommRing S] [Algebra K S] {w : pts S} (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R) (hy : mapR φ y w) :
    evalAt pts mapR f w = φ (f p y) := by
  have hF : FromTest pts mapR w := ⟨p, φ, y, hy⟩
  unfold evalAt
  rw [dif_pos hF]
  exact hWD f hf S _ _ _ _ _ _ w hF.choose_spec.choose_spec.choose_spec hy

theorem evalAt_congr_id (hWD : EvalWD pts mapR) (hTr : MapTransId pts mapR) {f : Rules pts}
    (hf : IsNatural pts mapR f) {S : Type} [CommRing S] [Algebra K S] {z w : pts S}
    (h₁ : mapR (AlgHom.id K S) z w) (h₂ : mapR (AlgHom.id K S) w z) :
    evalAt pts mapR f z = evalAt pts mapR f w := by
  by_cases hz : FromTest pts mapR z
  · obtain ⟨p, φ, y, hy⟩ := hz
    rw [evalAt_eq_lemma hWD hf p φ y hy, evalAt_eq_lemma hWD hf p φ y (hTr _ _ φ y z w hy h₁)]
  · have hw : ¬ FromTest pts mapR w := fun hw' => hz (fromTest_of_id hTr h₂ hw')
    unfold evalAt
    rw [dif_neg hz, dif_neg hw]

theorem evalAt_actL (hL : ActLaws pts mapR borR actR) (hWD : EvalWD pts mapR)
    (hTr : MapTransId pts mapR) (g : G) {f : Rules pts} (hf : IsNatural pts mapR f) {S : Type}
    [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (actL pts actR g f) y = evalAt pts mapR f (mvPt pts actR g y) := by
  have hm : ∀ (g' : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S), actR g' y (mvPt pts actR g' y) := by
    intro g' S _ _ y
    unfold mvPt
    rw [dif_pos (hL.total g' S y)]
    exact (hL.total g' S y).choose_spec
  by_cases hF : FromTest pts mapR y
  · have hc := hF.choose_spec.choose_spec.choose_spec
    rw [evalAt_eq_lemma hWD hf _ _ _ (hL.nat g _ _ _ _ _ _ _ hc (hm g _) (hm g y))]
    unfold evalAt
    rw [dif_pos hF]
    rfl
  · have hmy : ¬ FromTest pts mapR (mvPt pts actR g y) := by
      rintro ⟨p, φ, z0, hz⟩
      apply hF
      have h1 := hL.nat g⁻¹ _ _ _ _ _ _ _ hz (hm g⁻¹ z0) (hm g⁻¹ (mvPt pts actR g y))
      have h2 := hL.mul g g⁻¹ _ _ _ _ (hm g y) (hm g⁻¹ (mvPt pts actR g y))
      first
        | rw [mul_inv_cancel] at h2
        | rw [mul_right_inv] at h2
      have h3 := hL.func 1 _ _ _ _ h2 (hL.one _ y)
      exact ⟨p, φ, _, hTr _ _ φ _ _ _ h1 h3⟩
    unfold evalAt
    rw [dif_neg hF, dif_neg hmy]

end Abstract

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem spMap_algHom_id (K : Type) [Field K] (T : Type) [CommRing T] [Algebra K T] :
    spMap (AlgHom.id K T).toRingHom = 𝟙 _ := by
  unfold spMap
  have h : CommRingCat.ofHom (AlgHom.id K T).toRingHom = 𝟙 (CommRingCat.of T) := rfl
  rw [h, Spec.map_id]
  try rfl

theorem dualMap_id (T : Type) [CommRing T] : dualMap (RingHom.id T) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x

theorem frMap_trans_id {c : Coeff l} :
    MapTransId (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) := by
  intro S T _ _ _ _ φ y z w hyz hzw
  obtain ⟨hx1, hu1, pm1, hs1, hf1, hsec1⟩ := hyz
  obtain ⟨hx2, hu2, pm2, hs2, hf2, hsec2⟩ := hzw
  have e1 : spMap (AlgHom.id c.F T).toRingHom = 𝟙 _ := spMap_algHom_id c.F T
  have e2 : spMap (dualMap (AlgHom.id c.F T).toRingHom) = 𝟙 _ := by
    have hd : dualMap (AlgHom.id c.F T).toRingHom = RingHom.id _ := dualMap_id T
    rw [hd]
    unfold spMap
    have h0 : CommRingCat.ofHom (RingHom.id (TrivSqZeroExt T T)) = 𝟙 (CommRingCat.of (TrivSqZeroExt T T)) := rfl
    rw [h0, Spec.map_id]
    try rfl
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, e1, Category.id_comp, hx1]
  · intro τ i
    rw [hu2, e2, Category.id_comp, hu1]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, e1]
    first
      | erw [Category.id_comp]
      | simp
      | rfl
  · intro i h
    have h2 := ppx_le pm2 hs2 i
    have h1 := ppx_le pm1 hs1 i
    rw [← hsec2 i h2, ← hsec1 i h1]
    first
      | rw [← Scheme.appLE_comp_appLE pm2 pm1 _ _ _ h1 h2]; rfl
      | rw [← Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1 h2]; rfl

theorem levActR_res {c c' : Coeff l} (hle : c.F ≤ c'.F) {G : Type}
    (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (g : G) {S : Type} [CommRing S]
    [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) {y y' : FrPt Xo c' S}
    (hy : levActR (Xo := Xo) (c := c') lev g y y') :
    levActR (Xo := Xo) (c := c) lev g (y.res hle h) (y'.res hle h) := by
  obtain ⟨ρ, ν, hi, hl, hm⟩ := hy
  exact ⟨ρ, ν, hi, hl, hm⟩

end Frames

section ActBC

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem actBC_of {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hWD' : EvalWD (K := c'.F) (fun S _ _ => FrPt Xo c' S) (fun φ y z => FrMap φ y z))
    (hL : ActLev (Xo := Xo) c lev) (hL' : ActLev (Xo := Xo) c' lev) :
    ActBC hle (actLev (Xo := Xo) c lev) (actLev (Xo := Xo) c' lev) := by
  intro a n g m as fs f' hf' hfs hBC S _ _ _ h y
  obtain ⟨hn', -⟩ := hf'
  have hn : ∀ i, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fs i) := by
    intro i
    obtain ⟨hni, -⟩ := hfs i
    exact hni
  have hTr := frMap_trans_id (Xo := Xo) (c := c)
  have hTr' := frMap_trans_id (Xo := Xo) (c := c')
  simp only [IsBC, evR, actLev] at hBC ⊢
  rw [evalAt_actL hL' hWD' hTr' g hn', hBC S h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [evalAt_actL hL hWD hTr g (hn i)]
  congr 1
  have A0 : levActR (Xo := Xo) (c := c') lev g y (mvPt (K := c'.F) (fun S _ _ => FrPt Xo c' S)
      (fun {S : Type} [CommRing S] [Algebra c'.F S] (g' : G) (y y' : FrPt Xo c' S) =>
        levActR (Xo := Xo) (c := c') lev g' y y') g y) := by
    unfold mvPt
    rw [dif_pos (hL'.total g S y)]
    exact (hL'.total g S y).choose_spec
  have A := levActR_res hle lev g h A0
  have B : levActR (Xo := Xo) (c := c) lev g (y.res hle h) (mvPt (K := c.F) (fun S _ _ => FrPt Xo c S)
      (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) =>
        levActR (Xo := Xo) (c := c) lev g' y y') g (y.res hle h)) := by
    unfold mvPt
    rw [dif_pos (hL.total g S (y.res hle h))]
    exact (hL.total g S (y.res hle h)).choose_spec
  exact evalAt_congr_id hWD hTr (hn i) (hL.func g _ _ _ _ A B) (hL.func g _ _ _ _ B A)

end ActBC

section Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

variable (Xo) in

def SecBC : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f' ∈ sec Xo c' a n,
    ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ sec Xo c a n) ∧ IsBC hle f' as fs

theorem evR_sum_smul {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {m : ℕ} (t : Fin m → c.F)
    (g : Fin m → Rul Xo c) :
    evR Xo c (∑ i, t i • g i) y = ∑ i, algebraMap c.F S (t i) * evR Xo c (g i) y := by
  unfold evR
  by_cases h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
  · simp only [evalAt, dif_pos h]
    simp [Finset.sum_apply, map_sum, Algebra.smul_def]
  · simp only [evalAt, dif_neg h]
    simp

theorem isBC_regroup [Algebra c.F c'.F] (halg : algebraMap c.F c'.F = incF c c' hle) {m d : ℕ}
    {f' : Rul Xo c'} {as : Fin m → c'.F} {gs : Fin m → Rul Xo c} (hBC : IsBC hle f' as gs)
    (B : Module.Basis (Fin d) c.F c'.F) :
    IsBC hle f' (fun j => B j) (fun j => ∑ i, (B.repr (as i) j) • gs i) := by
  intro S _ _ _ h y
  have h' : ∀ a : c.F, algebraMap c'.F S (incF c c' hle a) = algebraMap c.F S a := h
  rw [hBC S h y]
  simp_rw [evR_sum_smul, ← h', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← B.sum_repr (as i)]
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, halg, map_mul]
  ring

open Classical in
theorem rdU_unfBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hBC : IsBC hle f' as fs) :
    rdU (unfBC hle U σ') f' = ∑ i, σ' (as i) • rdU (U (σ'.comp (incF c c' hle))) (fs i) := by
  refine funext fun (k : (U (σ'.comp (incF c c' hle))).Comp) =>
    funext fun (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) => ?_
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  show (if h : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom then
      toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, h⟩)) else 0) =
    ∑ i, σ' (as i) * (if h : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom then
      toC (evR Xo c (fs i) ((U (σ'.comp (incF c c' hle))).un k ⟨x, h⟩)) else 0)
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · simp only [dif_pos hx]
    exact @hBC (CAt σ') _ ((σ'.comp (incF c c' hle)).toAlgebra) σ'.toAlgebra (fun _ => rfl) _
  · simp only [dif_neg hx, mul_zero, Finset.sum_const_zero]

theorem laU_unfBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    laU (unfBC hle U σ') a n = laU (U (σ'.comp (incF c c' hle))) a n := by
  rfl

theorem goodEmb_ext {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {σ' : c'.F →+* ℂ}
    (h : σ'.comp (incF c c' hle) = σ) : GoodEmb c' σ' := by
  unfold GoodEmb at hσ ⊢
  rw [← hσ, ← h]
  first
    | rfl
    | simp [incF]

theorem cuspBC_of (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hS : SecBC Xo hle) : CuspBC hle U := by
  classical
  intro a n f' hf'
  rw [mem_cusp] at hf'
  obtain ⟨hsec, hcusp⟩ := hf'
  obtain ⟨m, as, gs, hgs, hBC⟩ := hS a n f' hsec
  letI alg : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ c.F c'.F
  let B := Module.finBasis c.F c'.F
  let hs : Fin (Module.finrank c.F c'.F) → Rul Xo c := fun j => ∑ i, (B.repr (as i) j) • gs i
  have hBC' : IsBC hle f' (fun j => B j) hs := isBC_regroup hle rfl hBC B
  refine ⟨_, fun j => B j, hs, fun j => ?_, hBC'⟩
  rw [mem_cusp]
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgs i), fun σ hσ => ?_⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  have key : ∀ τ : c'.F →ₐ[c.F] ℂ,
      ∑ i, τ (B i) • rdU (U σ) (hs i) ∈ holSub (U σ).X (laU (U σ) a n) := by
    intro τ
    have hτ : τ.toRingHom.comp (incF c c' hle) = σ := RingHom.ext fun x => τ.commutes x
    have hm : ∑ i, τ.toRingHom (B i) • rdU (U (τ.toRingHom.comp (incF c c' hle))) (hs i) ∈
        holSub (U (τ.toRingHom.comp (incF c c' hle))).X (laU (U (τ.toRingHom.comp (incF c c' hle))) a n) := by
      have := hcusp τ.toRingHom (goodEmb_ext hle hσ hτ)
      rw [rdU_unfBC hle U τ.toRingHom hBC', laU_unfBC] at this
      exact this
    rw [hτ] at hm
    exact hm
  let Bd := (Algebra.traceForm c.F c'.F).dualBasis (traceForm_nondegenerate c.F c'.F) B
  have hinv : rdU (U σ) (hs j) =
      ∑ τ : c'.F →ₐ[c.F] ℂ, τ (Bd j) • ∑ i, τ (B i) • rdU (U σ) (hs i) := by
    have e1 : ∀ τ : c'.F →ₐ[c.F] ℂ, τ (Bd j) • ∑ i, τ (B i) • rdU (U σ) (hs i) =
        ∑ i, τ (Bd j * B i) • rdU (U σ) (hs i) := by
      intro τ
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, map_mul]
    rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_comm]
    have e2 : ∀ i, ∑ τ : c'.F →ₐ[c.F] ℂ, τ (Bd j * B i) • rdU (U σ) (hs i) =
        (if i = j then (1 : ℂ) else 0) • rdU (U σ) (hs i) := by
      intro i
      rw [← Finset.sum_smul, ← trace_eq_sum_embeddings (K := c.F) (L := c'.F) (E := ℂ),
        ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun i _ => e2 i]
    simp
  rw [hinv]
  exact Submodule.sum_mem _ fun τ _ => Submodule.smul_mem _ _ (key τ)

end Cusp

end Formalism.L2.Pj
