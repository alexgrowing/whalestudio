import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsGeometricPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.RankZeroFamily

open RankZero

theorem isIso_of_no_two_torsion {R : Type} [CommRing R] [IsDomain R] [CharZero R] {S : Scheme.{0}} [IsReduced S]
    (s : S ⟶ Sp R) [Flat s] (G : Over S) [GrpObj G] (hG : IsAbelianScheme G)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ G), g ^ 2 = 1 → g = 1) :
    IsIso G.hom := by
  have := hG.proper
  have := hG.smooth
  have := hG.comm
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have hcl := isClosedImmersion_of_section_of_isSeparated G.hom (eSec G) (section_w η[G])
  have hs : Surjective (eSec G) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨k, _, _, _, u, q, hu⟩ := FamTest.exists_geom_specializes (G.hom ≫ s) y
    refine (eSec G).isClosedEmbedding.isClosed_range.stableUnderSpecialization hu ?_
    let x := u ≫ G.hom
    have hp := isGrpPullback_pullback G x
    have hB := isAbelianScheme_pullback_obj x G hG
    have := hB.comm
    have ht := h k ((𝟙_ (Over (Sp k))).hom ≫ x)
    have hsB := surjective_unit GlobalTheory.card_torsion_abelianVariety _ hB one_lt_two (by simp) fun g hg => by
      have e := ht (pushHom hp _ g) (by rw [← map_pow, hg, map_one])
      rw [← map_one (pushHom hp (𝟙_ _))] at e
      exact Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
    obtain ⟨p, hp'⟩ := hsB (hp.1.lift u (𝟙 _) (Category.id_comp _).symm q)
    refine ⟨x p, ?_⟩
    have e₁ := congrArg (fun q => q p) (cubeMapOf hp).e_comm
    have e₂ := congrArg (fun r => r q) (hp.1.lift_fst u (𝟙 _) (Category.id_comp _).symm)
    exact e₁.symm.trans ((congrArg (pullback.fst G.hom x) hp').trans e₂)
  have : IsIso (eSec G) := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso (eSec G ≫ G.hom) := by
    rw [show eSec G ≫ G.hom = 𝟙 S from section_w η[G]]
    exact inferInstanceAs (IsIso (𝟙 S))
  exact IsIso.of_isIso_comp_left (eSec G) G.hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem fullObj_zero (hD : D.p + D.q = 0) {S : Scheme.{0}} (s : S ⟶ Sp (RZ H n N)) :
    FullObj D s (Inhab.zeroTriple H S) (fun _ => 1) := by
  have hz := isIso_zeroTriple (H := H) S
  have := subsingleton_La hD
  refine ⟨Inhab.isProper_zeroTriple S, (Out.Inh.zeroPolAV S).ample, fun _ _ _ _ _ => hom_unique hz _ _,
    fun _ _ => (_root_.mul_one _).symm, fun _ => rfl, fun k _ _ _ x β _ => ?_⟩
  obtain ⟨ζ, h₁, h₂, h₃⟩ := FamTest.exists_roots β
  refine ⟨fun τ => ⟨fun _ => lieMult_zero hz _ _ _ (by omega), fun _ => lieMult_zero hz _ _ _ (by omega)⟩,
    ⟨ζ, h₁, h₂, fun _ _ => 1, fun _ _ _ => hom_unique hz _ _, fun _ _ _ => hom_unique hz _ _,
      fun _ _ _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩,
      fun _ _ _ => ⟨fun _ => ⟨0, hom_unique hz _ _⟩, fun _ => hom_unique hz _ _⟩,
      fun _ _ _ _ _ => hom_unique hz _ _, fun m _ a b => ?_⟩, h₃, fun _ => hom_unique hz _ _⟩
  have e : unitOn (ζ m ^ D.EF a b) = 1 := by
    rw [Subsingleton.elim b 0, map_zero, zpow_zero, unitOn, map_one]
  rw [e]
  exact weilIs_zero hz (Inhab.zeroTriple H S).PP.isLB (triv_rig hz _) _ _ _

theorem isIso_fullObj (hD : D.p + D.q = 0) {S : Scheme.{0}} [IsReduced S] {s : S ⟶ Sp (RZ H n N)} [Flat s]
    {t : SAB H S} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)} (o : FullObj D s t lv) : IsIso t.G.hom := by
  refine isIso_of_no_two_torsion s _ ⟨t.semi.comm, t.semi.smooth, o.proper, t.semi.geomConnected⟩
    fun k _ _ _ x g hg => ?_
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨-, I, -⟩ := o.geom k x β hβ
  have := subsingleton_La hD
  obtain ⟨a, rfl⟩ := (I.onto 2 two_pos g).1 hg
  exact (I.ker 2 two_pos a).2 ⟨0, Subsingleton.elim _ _⟩

theorem famCore (hD : D.p + D.q = 0) (n N : ℕ) :
    FamCore D (𝟙 (Sp (RZ H n N))) (Inhab.zeroTriple H _) (fun _ => 1) := by
  refine ⟨inferInstance, inferInstance, isQProjOver_of_isIso _ inferInstance, inferInstance, fullObj_zero hD _,
    fun S s t lv hr _ hf o => ?_, fun k _ x _ _ _ _ e _ _ => by simpa using e⟩
  have hz := isIso_zeroTriple (H := H) (Sp (RZ H n N))
  obtain ⟨ν⟩ := nonempty_sabMap (isIso_fullObj hD o) hz s
  exact ⟨s, ⟨Category.comp_id _, ν, fun _ => sec_comm hz ν.cart.1.w _ _⟩,
    fun f hf => (Category.comp_id f).symm.trans hf.1⟩

theorem siegClause (hD : D.p + D.q = 0) (hn : n.Prime) {J : ℕ} (hJ : 1 ≤ J) :
    SiegClause D (𝟙 (Sp (RZ H n (n ^ J)))) (Inhab.zeroTriple H _) (fun _ => 1) := by
  intro p hp hpn
  have hz := isIso_zeroTriple (H := H) (Sp (RZ H n (n ^ J)))
  obtain ⟨Ag, bas, e₁, e₂⟩ := siegel_zero (H := H) GlobalTheory.card_torsion_abelianVariety hD
    (g := Module.finrank ℚ E / 2 * (D.p + D.q)) (by rw [hD, mul_zero]) hp (Nat.one_lt_pow (by omega) hn.one_lt)
    (((Nat.coprime_primes hn hp).2 hpn.symm).pow_left J)
  exact ⟨Ag, bas, e₁, fun O _ _ z b _ _ _ T sT f tT ν levT hpb _ => e₂ O z T sT tT levT
    (MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) hpb (inferInstanceAs (IsIso (𝟙 _))))
    (MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms _) ν.cart.1 hz)⟩

theorem siegRep {p : ℕ} (hp : p.Prime) (h₁ : 1 < N) (hN : N.Coprime p) :
    SiegRep (zeroFamily GlobalTheory.card_torsion_abelianVariety hp h₁ hN) :=
  ⟨isQProjOver_of_isIso _ (inferInstanceAs (IsIso (𝟙 _))), fun _ s o _ _ _ _ =>
    ⟨s, ⟨Category.comp_id _, siegPB_zero (isIso_sieg GlobalTheory.card_torsion_abelianVariety hp h₁ hN o) (isIso_unit _) _⟩,
      fun f hf => (Category.comp_id f).symm.trans hf.1⟩⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n J : ℕ), D.p + D.q = 0 → AuxiliaryInertOddPrime H n → 1 ≤ J → FamCore D (𝟙 (Sp (RZ H n (n ^ J)))) (Inhab.zeroTriple H _) (fun _ => 1) ∧ SiegClause D (𝟙 (Sp (RZ H n (n ^ J)))) (Inhab.zeroTriple H _) (fun _ => 1) ∧ ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily 0 p (n ^ J), SiegRep Ag :=
  fun _ _ _ _ _ _ _ _ _ J hD hn hJ => ⟨famCore hD _ _, siegClause hD hn.1 hJ, fun _ hp hpn =>
    ⟨_, siegRep hp (Nat.one_lt_pow (by omega) hn.1.one_lt) (((Nat.coprime_primes hn.1 hp).2 hpn.symm).pow_left J)⟩⟩

end GlobalTheory.Models.RankZeroFamily

end
