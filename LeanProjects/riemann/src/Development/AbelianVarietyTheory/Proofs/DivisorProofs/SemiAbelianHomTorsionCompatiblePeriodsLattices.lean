import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndomorphismTorusExtensionPeriodOfAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOfMumfordBundleIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two
open GlobalTheory.TorusExt

theorem periods_of_key : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ E E' : EndU U₁.toUnifPre, LBIso (cubeLB G₁ ![fst G₁ G₁ ≫ E.aG, snd G₁ G₁] U₁.LG.L) (cubeLB G₁ ![fst G₁ G₁, snd G₁ G₁ ≫ E'.aG] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ c, snd A₁.A A₁.A ≫ c] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], Key U₁.toUnifPre U₂.toUnifPre c b h F → ∃ φ : D₁.toPre.X →+ D₂.toPre.X, (∀ (y : D₁.toPre.X) (g : GtPtF D₁.toPre F), GtPtF.IsIota y g → ∃ g' : GtPtF D₂.toPre F, Act D₁.toPre D₂.toPre b h g g' ∧ GtPtF.IsIota (φ y) g') ∧ ∀ y, h (φ y) = E.h y := by
  intro R _ _ _ I hA D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hco E E' hE hW F _ _ _ hkey
  have hL := GlobalTheory.firstFiveLaws
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  letI := gtGroup D₁.toPre F
  letI := gtGroup D₂.toPre F
  have hB₁ := D₁.tau_bimult
  have hB₂ := D₂.tau_bimult
  have inj₂ := GlobalTheory.IotaInj.main hL R I hA D₂ F
  have dv₁ := (gt_onto_divisible_kernel hL R I hA D₁ F).2.1

  obtain ⟨ex, ad, tor⟩ := GlobalTheory.T.torusExtensionMap_welldefined_additive_characters R D₁.toPre D₂.toPre b h hlin.2.1 (fun χ => (hco χ).imp fun _ hu => hu.1) F
  choose mf hmf hmu using ex
  let m : GtPtF D₁.toPre F →+ GtPtF D₂.toPre F := AddMonoidHom.mk' mf fun x x' => (isAdd_iff_eq _ _ _).1
    (ad x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hmf x) (hmf x') (hmf _))
  have hm : ∀ x x', Act D₁.toPre D₂.toPre b h x x' ↔ x' = m x := fun x x' => ⟨hmu x x', fun e => e ▸ hmf x⟩

  have push : ∀ k : ℕ, 1 ≤ k → ∀ f₁ f₂, Tors U₁.toUnifPre F k f₁ → Tors U₂.toUnifPre F k f₂ → ∀ p : QkPt D₁.toPre F k,
      ∃ p' : QkPt D₂.toPre F k, p'.g = m p.g ∧ f₂ p' = f₁ p ≫ c ∧ GtPtF.IsIota p'.y (m (iota hB₁ F p.y)) := by
    intro k hk f₁ f₂ hf₁ hf₂ p
    obtain ⟨p', e₁, e₂⟩ := hkey k hk p (f₁ p) ((hf₁.1 _ _).2 rfl) (m p.g) ((hm _ _).2 rfl)
    refine ⟨p', e₁, ((hf₂.1 _ _).1 e₂).symm, (isIota_iff_eq hB₂ _ _).2 ?_⟩
    rw [← qk_nsmul hB₂ p', e₁, ← map_nsmul, qk_nsmul hB₁ p]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₁ A₁ G₁ hG₁ U₁ F 1 le_rfl
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₂ A₂ G₂ hG₂ U₂ F 1 le_rfl
  have ex₁ : ∀ y, ∃ y', GtPtF.IsIota y' (m (iota hB₁ F y)) := fun y => by
    obtain ⟨p', -, -, hp'⟩ := push 1 le_rfl f₁ f₂ hf₁ hf₂ (qkMk hB₁ y (iota hB₁ F y) (one_smul _ _))
    exact ⟨p'.y, hp'⟩
  choose φ₀ hφ₀ using ex₁
  let φ : D₁.toPre.X →+ D₂.toPre.X := AddMonoidHom.mk' φ₀ fun y y' => inj₂ _ _ _ (hφ₀ (y + y'))
    ((isIota_iff_eq hB₂ _ _).2 (by
      rw [map_add, map_add, map_add, ← (isIota_iff_eq hB₂ _ _).1 (hφ₀ y), ← (isIota_iff_eq hB₂ _ _).1 (hφ₀ y')]))
  have hφ : ∀ y, GtPtF.IsIota (φ y) (m (iota hB₁ F y)) := hφ₀
  refine ⟨φ, fun y g hg => ⟨m g, (hm _ _).2 rfl, ?_⟩, fun y => ?_⟩
  · rw [(isIota_iff_eq hB₁ _ _).1 hg]; exact hφ y
  refine GlobalTheory.KeyIota.eq_of_torsion_chars (F := F) fun k hk t ht => ?_
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₁ A₁ G₁ hG₁ U₁ F k hk
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₂ A₂ G₂ hG₂ U₂ F k hk
  have wp₁ := GlobalTheory.T.weilQk_pairing_existsUnique_torus hL R I hA D₁ F k hk
  have wp₂ := GlobalTheory.T.weilQk_pairing_existsUnique_torus hL R I hA D₂ F k hk
  have torp : ∀ p : QkPt D₁.toPre F k, f₁ p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U₁.toUnifPre.ext
    exact ((hf₁.1 p _).2 rfl w hw).1

  obtain ⟨gk, hgk⟩ := dv₁ k hk (iota hB₁ F y)
  let p : QkPt D₁.toPre F k := ⟨y, gk, _, hgk, (isIota_iff_eq hB₁ _ _).2 rfl⟩
  obtain ⟨p', -, hpp', hp'⟩ := push k hk f₁ f₂ hf₁ hf₂ p
  have hyp' : p'.y = φ y := inj₂ _ _ _ hp' (hφ y)

  have h0 : k • torusPt D₁.toPre F (Additive.ofMul t) = iota hB₁ F 0 := by
    rw [← map_nsmul, ← ofMul_pow, ht, ofMul_one, map_zero, map_zero]
  let q : QkPt D₁.toPre F k := qkMk hB₁ 0 (torusPt D₁.toPre F (Additive.ofMul t)) h0
  have hq : IsTor t q.g := (isTor_iff _ _).2 (isTorusPtF_torusPt t)
  obtain ⟨q', hqg, hqq', hq'i⟩ := push k hk f₁ f₂ hf₁ hf₂ q
  have hq'0 : q'.y = 0 := inj₂ _ _ _ hq'i ((isIota_iff_eq hB₂ _ _).2 (by
    show m (iota hB₁ F 0) = iota hB₂ F 0
    simp only [map_zero]))
  have hq'tor : IsTor (t.comp (AddMonoidHom.toMultiplicative h)) q'.g := tor t q.g q'.g hq ((hm _ _).2 hqg)

  have ec := GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hA D₁ A₁ G₁ hG₁ U₁ F E E E
  have adE := ec.2.1
  choose aEf haE huE using ec.1
  let aE : GtPtF D₁.toPre F →+ GtPtF D₁.toPre F := AddMonoidHom.mk' aEf fun x x' => (isAdd_iff_eq _ _ _).1
    (adE x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (haE x) (haE x') (haE _))
  have hqE0 : k • aE q.g = iota hB₁ F 0 := by
    rw [← map_nsmul]
    show aE (k • torusPt D₁.toPre F (Additive.ofMul t)) = _
    simp only [h0, map_zero]
  let qE : QkPt D₁.toPre F k := qkMk hB₁ 0 (aE q.g) hqE0
  have hqEtor : IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) qE.g := ec.2.2.1 t q.g qE.g hq (haE q.g)
  have hFu := (GlobalTheory.UT.functorial_of_unif R I hA D₁ A₁ G₁ hG₁ U₁).2 E E' hE
  have hqE : f₁ qE = f₁ q ≫ E.aA := ((hf₁.1 _ _).1 ((hFu.2 F).2.2 k hk q qE (f₁ q)
    (by show (0 : D₁.toPre.X) = E'.h 0; rw [map_zero]) (haE q.g) ((hf₁.1 _ _).2 rfl))).symm

  have w₁ := (hf₁.2.2.2.2 _ _ _).1 ((wp₁ qE p).2 (t.comp (AddMonoidHom.toMultiplicative E.h)) rfl hqEtor)
  rw [hqE, ← Category.comp_id (f₁ p)] at w₁
  have w₂ := (GlobalTheory.T.commutator_pairing_eq_of_mumford_bundle_iso _ A₁ A₂ A₁ c c E.aA (𝟙 _) hc hc E.homA inferInstance hW F _ k (f₁ q) (f₁ p)
    (torp q) (torp p) _).2 w₁
  rw [← hqq', ← hpp'] at w₂
  have w₃ := (hf₂.2.2.2.2 _ _ _).2 w₂
  have e := (wp₂ q' p').1.unique w₃ ((wp₂ q' p').2 _ hq'0 hq'tor)
  rw [hyp'] at e
  exact e.symm

end GlobalTheory.Mum.Two
