import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalTateIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionTateStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.TauTwist GlobalTheory.ArcBuild

noncomputable section

namespace GlobalTheory.ArcBuildTate

theorem untwisted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → ∀ (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (r : O), ((β r : c.F) : ℂ) = zeta l.A → letI := H.starRing; ∃ I : TateIsoQ D P.D.toPre P.oD F, (I.ζ l.A : F) = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b r) ∧ (∀ a q, QkExt (algebraMap _ F) (hL.1 a).choose q → Out.QkPt.Equiv P.D.toPre F q (I.ev l.A a)) ∧ ∀ a (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)), ∀ q, QkExt (algebraMap _ F) (hL.2 a ha).choose q → Out.QkPt.Equiv P.D.toPre F q (I.ev l.M a) := by
  intro E _ _ _ H D l Xo c O _ β Y T io b y z h₁ h₂ h₃ h₄ t m P hP hL F _ _ _ r hr
  letI := H.starRing
  obtain ⟨J, j₁, j₂, j₃⟩ := GlobalTheory.T.dvr_arc_extension_tate E H D l Xo c O β Y T io b y z h₁ h₂ h₃ h₄ t m P hL F r hr
  obtain ⟨I, i₁, i₂⟩ := GlobalTheory.T.exists_rational_tate_isomorphism E H D T t P hP F J
  refine ⟨I, by rw [i₁]; exact j₁, fun a q hq => i₂ l.A l.A_pos a q (j₂ a q hq), fun a ha q hq => ?_⟩
  exact i₂ l.M (lt_of_lt_of_le (by decide) l.three_le) a q (j₃ a ha q hq)

theorem twisted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (y : Sp T.V ⟶ Y.X) (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t) (ϖ : T.V) (hϖ : Irreducible ϖ) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.ArcBuild.beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F], letI := H.starRing; ∀ (I : TateIsoQ D P.D.toPre P.oD F), (∀ a q, QkExt (algebraMap _ F) (hL.1 a).choose q → Out.QkPt.Equiv P.D.toPre F q (I.ev l.A a)) → (∀ a (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)), ∀ q, QkExt (algebraMap _ F) (hL.2 a ha).choose q → Out.QkPt.Equiv P.D.toPre F q (I.ev l.M a)) → ∃ I' : TateIsoQ D (GlobalTheory.ArcBuild.D0 P hϖ) (GlobalTheory.ArcBuild.oa0 P hϖ) F, I'.ζ = I.ζ ∧ (∀ a q, QkExt (algebraMap _ F) (GlobalTheory.ArcBuild.twistedLevelPointsOfLattice P hϖ Y y m hdiv hL a) q → Out.QkPt.Equiv (GlobalTheory.ArcBuild.D0 P hϖ) F q (I'.ev l.A a)) ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ q, QkExt (algebraMap _ F) (GlobalTheory.ArcBuild.eta0 P hϖ Y y m hdiv hL a) q → Out.QkPt.Equiv (GlobalTheory.ArcBuild.D0 P hϖ) F q (I'.ev l.M a) := by
  intro E _ _ _ H D l Xo c O _ β Y T y t m P ϖ hϖ hdiv hL F _ _ _
  letI := H.starRing
  intro I e₂ e₃
  have hw := GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)
  have ht := isScalarForm_tF P hϖ
  have hq := psiRel0 P hϖ
  have hR := isRootForm_rF P hϖ (dvd_of_dvd P hϖ (dvd_refl l.M') hdiv)
  let s : P.D.toPre.X → P.D.toPre.X → Fˣ := fun y x =>
    Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (rF P hϖ l.M' y x)
  have hs : IsRootForm (𝓞 E) l.M' (tF P hϖ) s :=
    ⟨hR.1.map _, fun y x => by
      show (Units.map _ _) ^ _ = _
      rw [← map_pow, hR.2 y x]
      rfl⟩
  obtain ⟨s', I', s₁, -, s₃, s₄, s₅⟩ := exists_tateIsoQ_twist P.D.tau_bimult hw ht P.oD l.M' s hs I
  have lev : ∀ {k : ℕ} (hk : 0 < k) (hd : k ∣ l.M') (p : QkPt P.D.toPre (FractionRing T.V) k) (v : D.La),
      (∀ q, QkExt (algebraMap _ F) p q → QkPt.Equiv P.D.toPre F q (I.ev k v)) → ∀ q',
      QkExt (algebraMap _ F) (qkScale hw ht hq (isRootForm_rF P hϖ (dvd_of_dvd P hϖ hd hdiv)) _ p) q' →
      QkPt.Equiv (D0 P hϖ) F q' (I'.ev k v) := by
    intro k hk hd p v he q' hq'
    obtain ⟨q, rfl⟩ := (qkScaleEquiv hw ht hq (s₁ k hk) _).surjective q'
    have e := qkRel_qkScaleEquiv (D := P.D.toPre) (hψ := (D0 P hϖ).psi_gen) hw ht hq (s₁ k hk) q
    refine e.equiv hw ht hq (s₁ k hk) (s₅ k hk v) (he q (QkRel.qkExt_of (fun y x => ?_)
      (qkRel_qkScale hw ht hq (isRootForm_rF P hϖ (dvd_of_dvd P hϖ hd hdiv)) p) e hq'))
    rw [s₃ k hk hd]
    show (Units.map _ _) ^ _ = _
    rw [← map_pow]
    congr 1
    obtain ⟨j, hj⟩ := dvd_of_dvd P hϖ (dvd_refl l.M') hdiv y x
    obtain ⟨i, hi⟩ := hd
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
    have hi0 : (i : ℤ) ≠ 0 := by
      rintro h
      have : i = 0 := by exact_mod_cast h
      rw [this, mul_zero] at hi
      omega
    simp only [rF, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hj, hi, Nat.mul_div_cancel_left _ hk]
    push_cast
    rw [Int.mul_ediv_cancel_left _ (mul_ne_zero hk0 hi0), mul_assoc, Int.mul_ediv_cancel_left _ hk0]
    ring
  refine ⟨I', s₄, fun v => lev l.A_pos (Nat.dvd_lcm_right l.M l.A) _ v (e₂ v), fun v hv q hq => ?_⟩
  rw [GlobalTheory.ArcBuild.eta0, dif_pos hv] at hq
  exact lev (lt_of_lt_of_le (by decide) l.three_le) (Nat.dvd_lcm_left l.M l.A) _ v (e₃ v hv) q hq

theorem tateCl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → ∀ (ϖ : T.V) (hϖ : Irreducible ϖ) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.ArcBuild.beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P), GlobalTheory.ArcBuild.TateCl P hϖ Y b y m hdiv hL := by
  intro E _ _ _ H D l Xo c O _ β Y T io b y z h₁ h₂ h₃ h₄ t m P hP ϖ hϖ hdiv hL
  letI := H.starRing
  intro F _ _ _ r hr
  obtain ⟨I, e₁, e₂, e₃⟩ := untwisted E H D l Xo c O β Y T io b y z h₁ h₂ h₃ h₄ t m P hP hL F r hr
  obtain ⟨I', f₁, f₂, f₃⟩ := twisted E H D l Xo c O β Y T y t m P ϖ hϖ hdiv hL F I e₂ e₃
  exact ⟨I', by rw [f₁]; exact e₁, f₂, f₃⟩

end GlobalTheory.ArcBuildTate
