import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.AbelianLocusMap

theorem isFinite_lift_comp {Y C Z A A' A'' : Scheme.{0}} (g : Y ⟶ C) (q : C ⟶ Z) (sY : Y ⟶ A'') (sC : C ⟶ A')
    (sZ : Z ⟶ A) (u : A'' ⟶ A') (v : A' ⟶ A) (z : A'' ⟶ A) (hz : u ≫ v = z) (w₁ : g ≫ sC = sY ≫ u)
    (w₂ : q ≫ sZ = sC ≫ v) (w : (g ≫ q) ≫ sZ = sY ≫ z) (h₁ : IsFinite (pullback.lift g sY w₁))
    (h₂ : IsFinite (pullback.lift q sC w₂)) : IsFinite (pullback.lift (g ≫ q) sY w) := by
  have hκ : pullback.fst sZ z ≫ sZ = (pullback.snd sZ z ≫ u) ≫ v := by
    rw [pullback.condition, Category.assoc, hz]
  have hψ : (pullback.fst sC u ≫ q) ≫ sZ = pullback.snd sC u ≫ z := by
    rw [Category.assoc, w₂, ← Category.assoc, pullback.condition, Category.assoc, hz]
  have hbot : IsPullback (pullback.lift _ _ hκ) (pullback.snd sZ z) (pullback.snd sZ v) u := by
    refine IsPullback.of_right (h₁₂ := pullback.fst sZ v) (h₂₂ := v) (v₁₃ := sZ) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback sZ v)
    rw [pullback.lift_fst, hz]
    exact IsPullback.of_hasPullback sZ z
  have htop : IsPullback (pullback.fst sC u) (pullback.lift _ _ hψ) (pullback.lift q sC w₂)
      (pullback.lift _ _ hκ) := by
    refine IsPullback.of_bot ?_ ?_ hbot
    · rw [pullback.lift_snd, pullback.lift_snd]
      exact IsPullback.of_hasPullback sC u
    · apply pullback.hom_ext
      · simp only [pullback.lift_fst, Category.assoc]
      · simp only [pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc]
        exact pullback.condition
  have hfin : IsFinite (pullback.lift _ _ hψ) :=
    MorphismProperty.of_isPullback (P := @IsFinite) htop h₂
  have heq : pullback.lift (g ≫ q) sY w = pullback.lift g sY w₁ ≫ pullback.lift _ _ hψ := by
    apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, Category.assoc]
  rw [heq]
  infer_instance

theorem isFinite_lift_restrict {Y Z U V A A' : Scheme.{0}} {g : Y ⟶ Z} {gU : U ⟶ V} {i : U ⟶ Y} {i' : V ⟶ Z}
    (p : IsPullback gU i i' g) (sY : Y ⟶ A') (sZ : Z ⟶ A) (z : A' ⟶ A) (w : g ≫ sZ = sY ≫ z)
    (w' : gU ≫ i' ≫ sZ = (i ≫ sY) ≫ z) (h : IsFinite (pullback.lift g sY w)) :
    IsFinite (pullback.lift gU (i ≫ sY) w') := by
  have hκ : (pullback.fst (i' ≫ sZ) z ≫ i') ≫ sZ = pullback.snd (i' ≫ sZ) z ≫ z := by
    rw [Category.assoc, pullback.condition]
  have hbot : IsPullback (pullback.lift _ _ hκ) (pullback.fst (i' ≫ sZ) z) (pullback.fst sZ z) i' := by
    refine IsPullback.of_right (h₁₂ := pullback.snd sZ z) (h₂₂ := sZ) (v₁₃ := z) ?_
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback sZ z).flip
    rw [pullback.lift_snd]
    exact (IsPullback.of_hasPullback (i' ≫ sZ) z).flip
  have htop : IsPullback i (pullback.lift gU (i ≫ sY) w') (pullback.lift g sY w) (pullback.lift _ _ hκ) := by
    refine IsPullback.of_bot ?_ ?_ hbot
    · rw [pullback.lift_fst, pullback.lift_fst]
      exact p.flip
    · apply pullback.hom_ext
      · simp only [pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc]
        exact p.w.symm
      · simp only [Category.assoc, pullback.lift_snd]
  exact MorphismProperty.of_isPullback (P := @IsFinite) htop h

def toRing {T : Scheme.{0}} {R : Type} [CommRing R] (u : T ⟶ Sp R) : R →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ u.appTop).hom

theorem toRing_inj {T : Scheme.{0}} {R : Type} [CommRing R] {u v : T ⟶ Sp R} (h : toRing u = toRing v) : u = v := by
  apply ext_of_isAffine
  have h' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ u.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ v.appTop := CommRingCat.hom_ext h
  exact (cancel_epi _).1 h'

theorem toRing_comp {T : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (u : T ⟶ Sp R') (b : R →+* R') :
    toRing (u ≫ spMap b) = (toRing u).comp b := by
  unfold toRing
  rw [Scheme.Hom.comp_appTop]
  change _ = (CommRingCat.ofHom b ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ u.appTop).hom
  rw [Scheme.ΓSpecIso_inv_naturality_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_RZ {T : Scheme.{0}} {l : Level H} {S A : ℕ} (hA : l.A = A) {β : RZ H S A →+* KA l}
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) (u v : T ⟶ Sp (KA l))
    (h : u ≫ spMap β = v ≫ spMap β) : u = v := by
  apply toRing_inj
  have h1 : (toRing u).comp β = (toRing v).comp β := by
    rw [← toRing_comp, ← toRing_comp, h]
  set f := toRing u
  set g := toRing v
  have hinv : ∀ x : KA l, f x = g x → f x⁻¹ = g x⁻¹ := by
    intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · have e1 : f x * f x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      have e2 : g x * g x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      calc f x⁻¹ = f x⁻¹ * (g x * g x⁻¹) := by rw [e2, _root_.mul_one]
        _ = (f x⁻¹ * f x) * g x⁻¹ := by rw [hx, _root_.mul_assoc]
        _ = g x⁻¹ := by rw [_root_.mul_comm (f x⁻¹), e1, _root_.one_mul]
  have hrange : ∀ (y : KA l) (r : RZ H S A), (y : ℂ) = (r : ℂ) → f y = g y := by
    intro y r e
    have hy : y = β r := Subtype.ext (by rw [e]; exact (hβ r).symm)
    rw [hy]
    exact RingHom.congr_fun h1 r
  have key : ∀ (x : ℂ) (hx : x ∈ IntermediateField.adjoin ℚ {H.rt0, zeta l.A}),
      f ⟨x, hx⟩ = g ⟨x, hx⟩ := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · have hm : (1 + H.rt0) / 2 ∈ RZ H S A := Subring.subset_closure (by simp)
        have hr : (1 + H.rt0) / 2 + (1 + H.rt0) / 2 - 1 ∈ RZ H S A :=
          sub_mem (add_mem hm hm) (one_mem _)
        exact hrange _ ⟨_, hr⟩ (by change H.rt0 = _; ring)
      · have hz : zeta l.A ∈ RZ H S A := by
          rw [hA]
          exact Subring.subset_closure (by simp)
        exact hrange _ ⟨_, hz⟩ rfl
    | algebraMap q =>
      change f (algebraMap ℚ (KA l) q) = g (algebraMap ℚ (KA l) q)
      exact RingHom.congr_fun (RingHom.ext_rat (f.comp (algebraMap ℚ (KA l)))
        (g.comp (algebraMap ℚ (KA l)))) q
    | add x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
    | inv x hx ih =>
      change f (⟨x, hx⟩⁻¹) = g (⟨x, hx⟩⁻¹)
      exact hinv _ ih
    | mul x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]
  ext x
  exact key x.1 x.2

theorem exists_isInc {O : Type} [CommRing O] (i : O →+* ℂ) (hi : Function.Injective i) {S S' A A' : ℕ}
    (b₀ : RZ H S A →+* O) (b₁ : RZ H S' A' →+* O) (h₀ : IsInc (RZ H S A).subtype i b₀)
    (h₁ : IsInc (RZ H S' A').subtype i b₁) : ∃ b : RZ H S A' →+* O, IsInc (RZ H S A').subtype i b := by
  have hle : RZ H S A' ≤ i.range := by
    apply Subring.closure_le.2
    intro z hz
    rcases hz with h | h | h
    · rw [h]
      exact RingHom.mem_range.2 ⟨b₀ ⟨(1 + H.rt0) / 2, Subring.subset_closure (Set.mem_insert _ _)⟩, h₀ _⟩
    · rw [h]
      exact RingHom.mem_range.2 ⟨b₀ ⟨(S : ℂ)⁻¹,
        Subring.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))⟩, h₀ _⟩
    · rw [Set.mem_singleton_iff.1 h]
      exact RingHom.mem_range.2 ⟨b₁ ⟨zeta A',
        Subring.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))⟩, h₁ _⟩
  let e := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun a b hab => hi (congrArg Subtype.val hab), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (Subring.inclusion hle), fun x => ?_⟩
  have hx := congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))
  exact hx

theorem exists_map_top (L₁ : Out.Laws) (L₂ : Out.Laws2) (L₃ : Out.Laws3) {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}
    {n N : ℕ} {T : Top Xo n N} (hN : ToroidalLevelCompatibility (H := H) (D := D)) {l₀ : Level H} (B : BaseModel T l₀) {l : Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model (Xo l) c β) (b : RZ H n N →+* O)
    (hd : l₀.Dvd l) (hNA : N ∣ l.A) (hβ : IsDedFrac β) (hb : IsInc (RZ H n N).subtype (c.F.val.toRingHom.comp β) b)
    (hR : Raises B Y) :
    ∃ (g : Y.X ⟶ T.Z) (hg : g ≫ T.s = Y.s ≫ spMap b) (mu : SABMap Y.t T.t g) (r' : (Xo l).XF c ⟶ (Xo B.l₁).X),
      IsFinite (pullback.lift g Y.s hg) ∧ Y.j ≫ g = r' ≫ T.a B.l₁ B.A_eq ∧
      ∀ x, (Y.oF.etaA x ^ (l.A / N)).left ≫ Y.m.φ ≫ mu.φ =
        r' ≫ ((Xo B.l₁).univ.etaA x).left ≫ (T.m B.l₁ B.A_eq).φ := by
  obtain ⟨b₀, r, ν, hb₀, hlev, ⟨a⟩⟩ := hR
  have hinjF : Function.Injective c.F.val.toRingHom := Subtype.val_injective
  have hinjO : Function.Injective (c.F.val.toRingHom.comp β) := by
    let _ := β.toAlgebra
    have _ := hβ.2.2
    exact hinjF.comp (IsFractionRing.injective O c.F)
  obtain ⟨b', hb'⟩ := exists_isInc (H := H) _ hinjO b₀ b hb₀ hb
  have hb₀eq : b₀ = b'.comp B.b := by
    ext x
    apply hinjO
    show _ = (c.F.val.toRingHom.comp β) (b' (B.b x))
    rw [hb₀ x, hb' (B.b x)]
    exact (B.b_inc x).symm
  subst hb₀eq
  have hd₁ : B.l₁.Dvd l := by
    refine ⟨?_, ?_, ?_⟩
    · rw [B.M_eq]; exact hd.1
    · rw [B.Mb_eq]; exact hd.2.1
    · rw [B.A_eq]; exact hNA
  obtain ⟨k, r', ν', hr, hk, hlev', -, -, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN B.l₁ l c Y.oF Y.m0 hd₁
  have hk' : β.comp b' = k.comp B.β₁ := by
    ext x
    show (c.F.val.toRingHom.comp β) (b' x) = c.F.val.toRingHom (k (B.β₁ x))
    rw [hb' x, hk (B.β₁ x), B.β₁_inc x]
  have hjY := GlobalTheory.Models.Cpt.openImmersion_comp_structure_eq_generic (ofModel Y)
  have hjC := GlobalTheory.Models.Cpt.openImmersion_comp_structure_eq_generic B.C
  have hjC₁ := GlobalTheory.Models.Cpt.openImmersion_comp_structure_eq_generic B.C₁
  have e1 : B.r ≫ (Xo l₀).s ≫ spMap B.β = (Xo B.l₁).s ≫ spMap B.β₁ ≫ spMap B.b := by
    rw [← hjC, ← Category.assoc, ← B.above.j_comm, Category.assoc, B.above.π_over,
      ← Category.assoc B.C₁.j, hjC₁, Category.assoc]
  have e2 : r ≫ (Xo l₀).s ≫ spMap B.β = pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫
      spMap β ≫ spMap (b'.comp B.b) := by
    rw [← hjC, ← Category.assoc, ← a.j_comm, Category.assoc, a.π_over, ← Category.assoc (ofModel Y).j, hjY,
      Category.assoc]
  have e3 : spMap β ≫ spMap (b'.comp B.b) = spMap k ≫ spMap B.β₁ ≫ spMap B.b := by
    rw [spMap_comp B.b b', ← Category.assoc (spMap β), ← spMap_comp, hk', spMap_comp, Category.assoc]
  have hs : (r' ≫ B.r) ≫ (Xo l₀).s = r ≫ (Xo l₀).s := by
    apply eq_of_RZ B.A_one B.β_inc
    simp only [Category.assoc]
    rw [e1, e2, ← Category.assoc r' (Xo B.l₁).s, hr, e3]
    simp only [Category.assoc]
  obtain ⟨ν'', hν''⟩ := GlobalTheory.LevelCover.sab_comp ν' B.ν rfl
  have hMM : l.M / l₀.M * (l₀.M / l₀.M) = l.M / l₀.M := by
    rcases Nat.eq_zero_or_pos l₀.M with h0 | h0
    · simp [h0]
    · rw [Nat.div_self h0, Nat.mul_one]
  have hlevC : LevComp Y.oF (Xo l₀).univ (r' ≫ B.r) ν'' := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hν'']
      calc (Y.oF.eta x ^ (l.M / l₀.M)).left ≫ ν'.φ ≫ B.ν.φ
          = ((Y.oF.eta x ^ (l.M / B.l₁.M)) ^ (B.l₁.M / l₀.M)).left ≫ ν'.φ ≫ B.ν.φ := by
            rw [← _root_.pow_mul, B.M_eq, hMM]
        _ = r' ≫ ((Xo B.l₁).univ.eta x ^ (B.l₁.M / l₀.M)).left ≫ B.ν.φ := by
            rw [← Category.assoc, GlobalTheory.LevelCover.sec_pow ν' _ _ (hlev'.1 x), Category.assoc]
        _ = (r' ≫ B.r) ≫ ((Xo l₀).univ.eta x).left := by
            rw [B.lev.1 x, Category.assoc]
    · rw [hν'', B.A_one, Nat.div_one]
      calc (Y.oF.etaA x ^ l.A).left ≫ ν'.φ ≫ B.ν.φ
          = ((Y.oF.etaA x ^ (l.A / B.l₁.A)) ^ N).left ≫ ν'.φ ≫ B.ν.φ := by
            rw [← _root_.pow_mul, B.A_eq, Nat.div_mul_cancel hNA]
        _ = r' ≫ ((Xo B.l₁).univ.etaA x ^ N).left ≫ B.ν.φ := by
            rw [← Category.assoc, GlobalTheory.LevelCover.sec_pow ν' _ _ (hlev'.2 x), Category.assoc]
        _ = (r' ≫ B.r) ≫ ((Xo l₀).univ.etaA x).left := by
            have h2 := B.lev.2 x
            rw [B.A_eq, B.A_one, Nat.div_one] at h2
            rw [h2, Category.assoc]
  have hred : IsReduced ((Xo l).XF c) := by
    have hsm0 : Smooth (Xo l).s := by
      have _ := (Xo l).smooth
      exact SmoothOfRelativeDimension.smooth D.dim (Xo l).s
    have hsm : Smooth (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) :=
      MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback _ _) hsm0
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ _ hsm).1
  obtain ⟨hrr, hνν⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l (Xo l₀) (KA l) (baseKA l)
    ((Xo l).XF c) _ Y.oF (r' ≫ B.r) r ν'' ν hred hs hlevC hlev
  have hj : (ofModel Y).j ≫ a.π = r' ≫ B.r ≫ B.C.j := by
    rw [a.j_comm, ← hrr, Category.assoc]
  have hm : (ofModel Y).m.φ ≫ a.mu.φ = ν'.φ ≫ B.ν.φ ≫ B.C.m.φ := by
    rw [a.φ_comm, ← hνν, hν'', Category.assoc]
  obtain ⟨h, mu', hh, -, -, hjh, hmh, hfin⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C B.C₁ (ofModel Y) B.b b' k B.r B.ν B.above r' ν' a.π a.mu a.π_over hβ hk' hr hj hm
  have hfin' := hfin a.fin
  obtain ⟨mu, hmu⟩ := GlobalTheory.LevelCover.sab_comp mu' B.qm rfl
  have hbb : b = b'.comp B.b' := by
    ext x
    apply hinjO
    show _ = (c.F.val.toRingHom.comp β) (b' (B.b' x))
    rw [hb x, hb' (B.b' x)]
    exact (B.b'_inc x).symm
  have hz : spMap b' ≫ spMap B.b' = spMap b := by rw [hbb, spMap_comp]
  have hg : (h ≫ B.q) ≫ T.s = Y.s ≫ spMap b := by
    show (h ≫ B.q) ≫ T.s = (ofModel Y).s ≫ spMap b
    rw [Category.assoc, B.q_over, ← Category.assoc, hh, Category.assoc, hz]
  refine ⟨h ≫ B.q, hg, mu, r', ?_, ?_, ?_⟩
  · exact isFinite_lift_comp h B.q _ B.C₁.s T.s (spMap b') (spMap B.b') (spMap b) hz hh B.q_over hg hfin' B.q_fin
  · show ((ofModel Y).j ≫ h ≫ B.q) = _
    rw [← Category.assoc, hjh, Category.assoc, B.q_j]
  · intro x
    have hl2 : (Y.oF.etaA x ^ (l.A / N)).left ≫ ν'.φ = r' ≫ ((Xo B.l₁).univ.etaA x).left := by
      have h2 := hlev'.2 x
      rwa [B.A_eq] at h2
    rw [hmu]
    show (Y.oF.etaA x ^ (l.A / N)).left ≫ (ofModel Y).m.φ ≫ mu'.φ ≫ B.qm.φ = _
    rw [← Category.assoc (ofModel Y).m.φ, hmh, Category.assoc, B.q_φ,
      ← Category.assoc (Y.oF.etaA x ^ (l.A / N)).left, hl2, Category.assoc]

theorem exists_finite_map : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β) (b : RZ H n N →+* O) (U : Y.X.Opens), 0 < n → (∃ e, N ∣ n ^ e) → l₀.Dvd l → N ∣ l.A → (n * l₀.M : O) ∈ Set.range (Units.val : Oˣ → O) → IsDedFrac β → IsInc (RZ H n N).subtype (c.F.val.toRingHom.comp β) b → Raises B Y → (U : Set Y.X) = abLocus Y.t.G → ∃ (f : U.toScheme ⟶ T.MM) (hf : f ≫ T.sM = (U.ι ≫ Y.s) ≫ spMap b) (tU : SAB H U.toScheme) (m₁ : SABMap tU Y.t U.ι) (m₂ : SABMap tU T.tM f), IsFinite (pullback.lift f _ hf) ∧ ∀ (x : D.La) (j' : (Xo l).XF c ⟶ U.toScheme) (y : (Xo l).XF c ⟶ tU.G.left), j' ≫ U.ι = Y.j → y ≫ m₁.φ = (Y.oF.etaA x ^ (l.A / N)).left ≫ Y.m.φ → y ≫ m₂.φ = j' ≫ f ≫ (T.lev x).left := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T hN l₀ B l c O _ β Y b U _ _ hd hNA _ hβ hb hR hU
  obtain ⟨g, hg, mu, r', hfin, hj, hlevel⟩ := exists_map_top L₁ L₂ L₃ hN B Y b hd hNA hβ hb hR
  have hUeq : U = g ⁻¹ᵁ T.U := by
    apply TopologicalSpace.Opens.ext
    rw [hU]
    ext x
    show x ∈ abLocus Y.t.G ↔ g x ∈ (T.U : Set T.Z)
    rw [T.U_eq]
    exact (abLocus_pullback abLocusOne T.t.semi mu.cart.1 x).symm
  subst hUeq
  have hpb := isPullback_morphismRestrict g T.U
  have hι : (g ∣_ T.U) ≫ T.U.ι = (g ⁻¹ᵁ T.U).ι ≫ g := morphismRestrict_ι g T.U
  have hf : ((g ∣_ T.U) ≫ T.u) ≫ T.sM = ((g ⁻¹ᵁ T.U).ι ≫ Y.s) ≫ spMap b := by
    simp only [Category.assoc]
    rw [T.u_over, ← Category.assoc (g ∣_ T.U), hι, Category.assoc, hg]
  have w₁ : (g ∣_ T.U) ≫ T.U.ι ≫ T.s = ((g ⁻¹ᵁ T.U).ι ≫ Y.s) ≫ spMap b := by
    rw [← Category.assoc (g ∣_ T.U), hι]
    simp only [Category.assoc]
    rw [hg]
  have h₁ := isFinite_lift_restrict hpb Y.s T.s (spMap b) hg w₁ hfin
  have w₂ : T.u ≫ T.sM = (T.U.ι ≫ T.s) ≫ 𝟙 _ := by rw [Category.comp_id, T.u_over]
  have h₂ : IsFinite (pullback.lift T.u (T.U.ι ≫ T.s) w₂) := by
    have e : pullback.lift T.u (T.U.ι ≫ T.s) w₂ = T.u ≫ inv (pullback.fst T.sM (𝟙 _)) := by
      rw [IsIso.eq_comp_inv, pullback.lift_fst]
    rw [e]
    have _ := T.u_fin
    infer_instance
  have hfinal := isFinite_lift_comp (g ∣_ T.U) T.u ((g ⁻¹ᵁ T.U).ι ≫ Y.s) (T.U.ι ≫ T.s) T.sM (spMap b) (𝟙 _)
    (spMap b) (Category.comp_id _) w₁ w₂ hf h₁ h₂
  have hcp : Out.CubePullSt := by
    first
    | exact L₁.cubePull
    | exact L₂.cubePull
    | exact L₃.cubePull
  have key : ∃ tU : SAB H (g ⁻¹ᵁ T.U).toScheme, Nonempty (SABMap tU Y.t (g ⁻¹ᵁ T.U).ι) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull hcp (g ⁻¹ᵁ T.U).ι Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨tU, ⟨m₁⟩⟩ := key
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.LevelCover.sab_comp m₁ mu rfl
  obtain ⟨m', hm'⟩ := GlobalTheory.LevelCover.sab_cancel T.mU n₁ (g ∣_ T.U) hι
  obtain ⟨m₂, hm₂⟩ := GlobalTheory.LevelCover.sab_comp m' T.mM rfl
  refine ⟨(g ∣_ T.U) ≫ T.u, hf, tU, m₁, m₂, hfinal, ?_⟩
  intro x j' y hj' hy
  have hKmem : ∀ z ∈ RZ H n N, z ∈ KA B.l₁ := by
    intro z hz
    have hrt : H.rt0 ∈ KA B.l₁ := IntermediateField.subset_adjoin ℚ _ (by simp)
    have hze : zeta N ∈ KA B.l₁ := by
      have e : zeta N = zeta B.l₁.A := by rw [B.A_eq]
      rw [e]
      exact IntermediateField.subset_adjoin ℚ _ (by simp)
    have h2 : (2 : ℂ) ∈ KA B.l₁ := by simp
    refine (Subring.closure_le (t := (KA B.l₁).toSubalgebra.toSubring)).2 ?_ hz
    intro w hw
    rcases hw with h | h | h
    · rw [h]
      show (1 + H.rt0) / 2 ∈ KA B.l₁
      exact div_mem (add_mem (one_mem _) hrt) h2
    · rw [h]
      show (n : ℂ)⁻¹ ∈ KA B.l₁
      exact inv_mem (natCast_mem _ n)
    · rw [Set.mem_singleton_iff.1 h]
      show zeta N ∈ KA B.l₁
      exact hze
  let β' : RZ H n N →+* KA B.l₁ := (RZ H n N).subtype.codRestrict (KA B.l₁) (fun z => hKmem z z.2)
  obtain ⟨W, fW, hW, -, -, hfa, -⟩ := T.fin B.l₁ B.A_eq β' (fun _ => rfl)
  have hrange : Set.range (T.a B.l₁ B.A_eq) ⊆ Set.range T.U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, T.U_eq, ← hfa]
    have h1 : W.ι (fW z) ∈ Set.range W.ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι, hW] at h1
    exact h1
  let a' := IsOpenImmersion.lift T.U.ι (T.a B.l₁ B.A_eq) hrange
  have ha' : a' ≫ T.U.ι = T.a B.l₁ B.A_eq := IsOpenImmersion.lift_fac _ _ _
  have hsec : ∀ {S : Scheme.{0}} {G : Over S} (z : 𝟙_ (Over S) ⟶ G), z.left ≫ G.hom = 𝟙 S :=
    fun z => Over.w z
  have hy'w : (((Xo B.l₁).univ.etaA x).left ≫ (T.m B.l₁ B.A_eq).φ) ≫ T.t.G.hom = a' ≫ T.U.ι := by
    rw [ha', Category.assoc, (T.m B.l₁ B.A_eq).cart.1.w, ← Category.assoc, hsec]
    exact Category.id_comp _
  let y' := T.mU.cart.1.lift _ _ hy'w
  have hy'1 : y' ≫ T.mU.φ = ((Xo B.l₁).univ.etaA x).left ≫ (T.m B.l₁ B.A_eq).φ :=
    T.mU.cart.1.lift_fst _ _ _
  have hy'2 : y' ≫ T.tU.G.hom = a' := T.mU.cart.1.lift_snd _ _ _
  have hlev := T.lev_eq B.l₁ B.A_eq a' x y' ha' hy'1
  have hYj : Y.j = Y.jQ ≫ pullback.fst _ _ := rfl
  have hyj : y ≫ tU.G.hom = j' := by
    rw [← cancel_mono (g ⁻¹ᵁ T.U).ι, Category.assoc, ← m₁.cart.1.w, ← Category.assoc y, hy, hj', hYj,
      Category.assoc, Y.m.cart.1.w, ← Category.assoc (Y.oF.etaA x ^ (l.A / N)).left, hsec]
    exact Category.id_comp _
  have hja : j' ≫ (g ∣_ T.U) = r' ≫ a' := by
    rw [← cancel_mono T.U.ι, Category.assoc, hι, ← Category.assoc j', hj', hj, Category.assoc, ha']
  have hym : y ≫ m'.φ = r' ≫ y' := by
    apply T.mU.cart.1.hom_ext
    · rw [Category.assoc, hm', hn₁, ← Category.assoc y, hy, Category.assoc, hlevel x, Category.assoc r', hy'1]
    · rw [Category.assoc, m'.cart.1.w, ← Category.assoc y, hyj, hja, Category.assoc r', hy'2]
  rw [hm₂, ← Category.assoc y, hym, Category.assoc r', hlev]
  simp only [Category.assoc]
  rw [← Category.assoc j', hja, Category.assoc]

end GlobalTheory.AbelianLocusMap

end
