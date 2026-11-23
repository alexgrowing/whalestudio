import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationUnimodularCompanionEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianLocalisationAdelicPointLatticeEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeFgOfFullStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG
open Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.PhiTLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locS_le_of_le {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (S : Submonoid R) {M M₁ : Submodule R W}
    (h : M ≤ Formalism.HermitianLatticesTheory.locS S M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, htx⟩ := h hx
  exact ⟨t * s, S.mul_mem ht hs, by rw [mul_smul]; exact htx⟩

theorem le_locS {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (S : Submonoid R) (M : Submodule R W) :
    M ≤ Formalism.HermitianLatticesTheory.locS S M := fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

theorem localization_eq_of_semilocalization_eq' {E : Type} [Field E] [NumberField E] [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    {Λ Λ₁ : Submodule (𝓞 E) (Fin n → E)} (h : Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal Λ₁) :
    Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ₁ := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := E) Q.asIdeal ≤ Q.asIdeal.primeCompl := by
    refine Submonoid.closure_le.2 ?_
    rintro s ⟨hs, -⟩
    exact hs
  have key : ∀ {M M₁ : Submodule (𝓞 E) (Fin n → E)}, Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal M = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal M₁ →
      Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M₁ := by
    intro M M₁ hM
    refine locS_le_of_le _ fun x hx => ?_
    have h1 : x ∈ Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal M₁ := hM ▸ le_locS _ M hx
    obtain ⟨t, ht, htx⟩ := h1
    exact ⟨t, hle ht, htx⟩
  exact le_antisymm (key h) (key h.symm)

theorem loc_mvL {E : Type} [Field E] [NumberField E] [StarRing E] (Q : Ideal (𝓞 E)) {n : ℕ} (g : GL (Fin n) E)
    {Λ Λ₁ : Submodule (𝓞 E) (Fin n → E)} (h : Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁) :
    Formalism.HermitianLatticesTheory.loc (K := E) Q (mvL g Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (mvL g Λ₁) := by
  have key : ∀ {M M₁ : Submodule (𝓞 E) (Fin n → E)}, Formalism.HermitianLatticesTheory.loc (K := E) Q M = Formalism.HermitianLatticesTheory.loc (K := E) Q M₁ →
      Formalism.HermitianLatticesTheory.loc (K := E) Q (mvL g M) ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q (mvL g M₁) := by
    intro M M₁ hM
    refine locS_le_of_le _ ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : y ∈ Formalism.HermitianLatticesTheory.loc (K := E) Q M₁ := hM ▸ le_locS _ M hy
    obtain ⟨t, ht, hty⟩ := h1
    refine ⟨t, ht, ⟨t • y, hty, ?_⟩⟩
    simp
  exact le_antisymm (key h) (key h.symm)

theorem exists_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ v : HeightOneSpectrum (𝓞 F), Formalism.L2.Col.IsOver v Q :=
  ⟨HeightOneSpectrum.under (𝓞 F) Q, rfl⟩

section SeamLoc
variable {D : D7} {X : Fields} (s : Seam D X) {n : ℕ}

theorem tr_smul (c : 𝓞 X.E) (x : Sp X.E n) :
    (fun i => s.iE ((c • x) i)) = RingOfIntegers.mapRingEquiv s.iE c • (fun i => s.iE (x i)) := by
  funext i
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
  rfl

theorem mem_lat_iff (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ ∃ x ∈ N, (fun i => s.iE (x i)) = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, N.zero_mem, by funext i; simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, N.add_mem ha hb, by funext i; simp⟩
    | smul r y _ hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • a, N.smul_mem _ ha, ?_⟩
      rw [tr_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem tr_inj : Function.Injective (fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) := by
  intro x y h
  funext i
  exact s.iE.injective (congrFun h i)

theorem mem_localization_lattice_iff (P : HeightOneSpectrum (𝓞 X.E)) (N : Submodule (𝓞 X.E) (Sp X.E n)) (x : Sp X.E n) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ (fun i => s.iE (x i)) ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  constructor
  · rintro ⟨c, hc, hcx⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE c, fun h => hc ((mem_seamP s P c).1 h), ?_⟩
    rw [← tr_smul]
    exact (mem_lat_iff s N _).2 ⟨_, hcx, rfl⟩
  · rintro ⟨d, hd, hdx⟩
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective d
    refine ⟨c, fun h => hd ((mem_seamP s P c).2 h), ?_⟩
    rw [← tr_smul] at hdx
    obtain ⟨x', hx', e⟩ := (mem_lat_iff s N _).1 hdx
    rw [tr_inj s e] at hx'
    exact hx'

theorem seam_locP (P : HeightOneSpectrum (𝓞 X.E)) (N N₁ : Submodule (𝓞 X.E) (Sp X.E n))
    (h : Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N₁) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N)) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N₁ = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  ext x
  rw [mem_localization_lattice_iff s P N₁ x, mem_localization_lattice_iff s P N x, h]

end SeamLoc

theorem loc_compan {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E))
    (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)) (hΛ : Λ.FG) (hΛ₁ : Λ₁.FG)
    (h : Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁) :
    Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) :=
  GlobalTheory.T.localization_unimodularCompanion_eq sp J a Q Λ Λ₁ hΛ hΛ₁ h

theorem loc_latAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (Q : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : Formalism.L2.Col.IsOver v Q)
    {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (h : bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x) :
    Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x₁ Lb) = Formalism.HermitianLatticesTheory.loc (K := E) Q.asIdeal (latAd x Lb) :=
  GlobalTheory.T.hermitianLocalisation_adelicPointLattice_eq hc Q v hv Lb hfin hspan x x₁ h

theorem latAd_fg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : (latAd x Lb).FG :=
  GlobalTheory.T.adelicPointLattice_fg_of_full Lb hfin hspan x

theorem phiT_lat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hTie j hj β x x₁ p p₁ hp hp₁ hx P
  have hSS := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1
  have hmem : seamP t.seam P.1 ∈ ssRec t u μ :=
    (mem_ssRec t u μ P.1).2 (by classical rw [hSS]; exact Finset.mem_union_left _ P.2)
  obtain ⟨v, hv⟩ := exists_over (F := D.host.F) (seamP t.seam P.1)
  have hxv := hx v ⟨_, hmem, hv⟩
  refine seam_locP t.seam P.1 _ _ ?_
  rw [hp₁.lat, hp.lat]
  refine localization_eq_of_semilocalization_eq' _ ?_
  unfold latCo
  refine loc_mvL _ _ ?_
  refine loc_compan _ _ _ _ _ _ (latAd_fg _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span _)
    (latAd_fg _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span _) ?_
  exact loc_latAd D.sp.cm _ v hv _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span _ _ hxv

end GlobalTheory.PhiTLat
