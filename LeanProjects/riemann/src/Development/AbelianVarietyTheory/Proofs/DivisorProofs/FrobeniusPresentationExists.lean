import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationMapMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoFlagLiftExists

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LB

namespace GlobalTheory.FrobPow

variable {X Y : Scheme.{0}}

section Pow

abbrev pwN (L : LB X) (n : ℕ) : LB X := ⟨L.ι, L.U, fun i j => L.g i j ^ (n : ℤ)⟩

variable {L M N : LB X} (n : ℕ)

theorem isLB_pwN (hL : L.IsLB) : (pwN L n).IsLB := AbLaw.isLB_pw hL n

theorem resG_pw_g (i j : L.ι) {W : X.Opens} (h : W ≤ L.U i ⊓ L.U j) :
    resG X h ((pwN L n).g i j).val =
      resG X h (L.g i j : Γ(X, L.U i ⊓ L.U j)) ^ n := by
  rw [← map_pow]
  exact congrArg _ ((congrArg Units.val (zpow_natCast (L.g i j) n)).trans
    (Units.val_pow_eq_pow_val _ _))

def powSec {V : X.Opens} (s : Γ(toMod L, V)) : Γ(toMod (pwN L n), V) :=
  mkSec (L := pwN L n) (fun i => coord s i ^ n) fun i j => by
    have h := congrArg (· ^ n) (coord_mem s i j)
    simp only [mul_pow] at h
    refine (map_pow _ _ _).trans (h.trans ?_)
    exact congrArg₂ (· * ·) (resG_pw_g (L := L) n i j _).symm (map_pow _ _ _).symm

theorem coord_powSec {V : X.Opens} (s : Γ(toMod L, V)) (i : L.ι) :
    coord (L := pwN L n) (powSec n s) i = coord s i ^ n := rfl

theorem powSec_smul {V : X.Opens} (a : Γ(X, V)) (s : Γ(toMod L, V)) :
    powSec n (a • s) = a ^ n • powSec n s :=
  sec_ext fun i => by
    change (resG X _ a * coord s i) ^ n = resG X _ (a ^ n) * coord s i ^ n
    rw [mul_pow, map_pow]

theorem powSec_map {V W : X.Opens} (h : W ≤ V) (s : Γ(toMod L, V)) :
    powSec n ((toMod L).presheaf.map (homOfLE h).op s) =
      (toMod (pwN L n)).presheaf.map (homOfLE h).op (powSec n s) :=
  sec_ext fun i => (map_pow (resG X (inf_le_inf_right (L.U i) h)) _ _).symm

theorem powSec_chartSec (hL : L.IsLB) (i : L.ι) :
    powSec n (LB.chartSec hL i) = LB.chartSec (isLB_pwN n hL) i :=
  sec_ext fun j => (resG_pw_g (L := L) n j i _).symm

def powHom (hL : L.IsLB) (φ : toMod L ⟶ toMod M) : toMod (pwN L n) ⟶ toMod (pwN M n) :=
  homOfFrames (isLB_pwN n hL) (σ := fun i => powSec n (φ.app (L.U i) (LB.chartSec hL i))) fun i j => by
    have h := congrArg (powSec n) ((isFrameFamily_chartSec hL).map φ i j)
    rw [powSec_smul, powSec_map, powSec_map] at h
    have e := resG_pw_g (L := L) n j i le_rfl
    rw [resG_self, resG_self] at e
    exact h.trans (congrArg (· • _) e.symm)

theorem powHom_app_powSec (hL : L.IsLB) (φ : toMod L ⟶ toMod M) {V : X.Opens}
    (s : Γ(toMod L, V)) : (powHom n hL φ).app V (powSec n s) = powSec n (φ.app V s) := by
  refine modSec_ext_of_cover (fun i => V ⊓ L.U i) (fun _ => inf_le_left)
    (le_iSup_inf hL.cover V) fun i => ?_
  rw [← app_modRes, ← powSec_map, ← powSec_map, ← app_modRes]
  obtain ⟨a, ha⟩ := (bijective_smul_chartSec hL i _ (inf_le_right : V ⊓ L.U i ≤ L.U i)).2
    ((toMod L).presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op s)
  rw [← ha]
  simp only []
  rw [powSec_smul, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, powSec_smul,
    powSec_map, app_modRes, app_modRes, powSec_map, powSec_chartSec]
  exact congrArg (fun t => a ^ n • (toMod (pwN M n)).presheaf.map _ t)
    (homOfFrames_app_chartSec (isLB_pwN n hL) _ i)

theorem powHom_comp (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ⟶ toMod M) (ψ : toMod M ⟶ toMod L)
    (g : Γ(X, ⊤)) (h : φ ≫ ψ = smulHom _ g) :
    powHom n hL φ ≫ powHom n hM ψ = smulHom _ (g ^ n) := by
  refine hom_ext_chartSec (isLB_pwN n hL) fun i => ?_
  rw [← powSec_chartSec n hL i, smulHom_app_apply, map_pow]
  change (powHom n hM ψ).app (L.U i) ((powHom n hL φ).app (L.U i) (powSec n (LB.chartSec hL i))) = _
  rw [powHom_app_powSec, powHom_app_powSec]
  refine Eq.trans ?_ (powSec_smul n _ _)
  exact congrArg (fun χ : toMod L ⟶ toMod L => powSec n (χ.app (L.U i) (LB.chartSec hL i))) h

end Pow

section Pull

variable {L M : LB X}

def pullMap (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X) (φ : toMod L ⟶ toMod M) :
    toMod (L.pull f) ⟶ toMod (M.pull f) :=
  (pullbackIso hL f).inv ≫ (Scheme.Modules.pullback f).map φ ≫ (pullbackIso hM f).hom

theorem pullMap_app_pullSec (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X) (φ : toMod L ⟶ toMod M)
    {V : X.Opens} (s : Γ(toMod L, V)) :
    (pullMap hL hM f φ).app (f ⁻¹ᵁ V) (pullSec L f V s) = pullSec M f V (φ.app V s) := by
  have h : toPushforward L f ≫ (Scheme.Modules.pushforward f).map (pullMap hL hM f φ) =
      φ ≫ toPushforward M f := by
    rw [← unit_comp_pullbackHom, ← unit_comp_pullbackHom, Category.assoc, ← Functor.map_comp,
      ← pullbackIso_hom hL, pullMap, Iso.hom_inv_id_assoc, Functor.map_comp, pullbackIso_hom]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality_assoc φ _)
  exact congrArg (fun χ => χ.app V s) h

theorem exists_iso_of_charts {ι : Type} {U U' : ι → Y.Opens} (g : ∀ i j, Γ(Y, U i ⊓ U j)ˣ)
    (g' : ∀ i j, Γ(Y, U' i ⊓ U' j)ˣ) (hU : U = U')
    (hg : ∀ i j (W : Y.Opens) (h : W ≤ U i ⊓ U j) (h' : W ≤ U' i ⊓ U' j),
      resG Y h (g i j).val = resG Y h' (g' i j).val) :
    ∃ e : toMod ⟨ι, U, g⟩ ≅ toMod ⟨ι, U', g'⟩, ∀ (V : Y.Opens) (s : Γ(toMod ⟨ι, U, g⟩, V))
      (j : ι) (W : Y.Opens) (h : W ≤ V ⊓ U j) (h' : W ≤ V ⊓ U' j),
      resG Y h' (coord (L := ⟨ι, U', g'⟩) (e.hom.app V s) j) =
        resG Y h (coord (L := ⟨ι, U, g⟩) s j) := by
  subst hU
  obtain rfl : g = g' := by
    funext i j
    have := hg i j _ le_rfl le_rfl
    rw [resG_self, resG_self] at this
    exact Units.ext this
  exact ⟨Iso.refl _, fun _ _ _ _ _ _ => rfl⟩

variable (n : ℕ) {π ι : Y ⟶ X} (hpre : ∀ V : X.Opens, π ⁻¹ᵁ V = ι ⁻¹ᵁ V)
  (hpow : ∀ (U : X.Opens) (W : Y.Opens) (e : W ≤ π ⁻¹ᵁ U) (e' : W ≤ ι ⁻¹ᵁ U) (a : Γ(X, U)),
    (π.appLE U W e).hom a = (ι.appLE U W e').hom a ^ n)

include hpow in

theorem exists_iso_pull (L : LB X) :
    ∃ e : toMod (L.pull π) ≅ toMod ((pwN L n).pull ι), ∀ (V : X.Opens) (s : Γ(toMod L, V)),
      e.hom.app (π ⁻¹ᵁ V) (pullSec L π V s) =
        (toMod ((pwN L n).pull ι)).presheaf.map (homOfLE (hpre V).le).op
          (pullSec (pwN L n) ι V (powSec n s)) := by
  have hU : (L.pull π).U = ((pwN L n).pull ι).U := funext fun j =>
    (pull_U π j).trans ((hpre _).trans (pull_U (L := pwN L n) ι j).symm)
  obtain ⟨e, he⟩ := exists_iso_of_charts (L.pull π).g ((pwN L n).pull ι).g hU fun i j W h h' => by
    refine (resG_pull_g π i j h).trans (Eq.trans ?_ (resG_pull_g (L := pwN L n) ι i j h').symm)
    refine (hpow (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) W _
      (h'.trans (inf_le_inf (pull_U_le (L := pwN L n) ι i) (pull_U_le (L := pwN L n) ι j))) _).trans
      ((map_pow _ _ _).symm.trans ?_)
    have e := resG_pw_g (L := L) n (i PUnit.unit) (j PUnit.unit) le_rfl
    rw [resG_self, resG_self] at e
    exact congrArg _ e.symm
  refine ⟨e, fun V s => sec_ext fun j => ?_⟩
  have h := he (π ⁻¹ᵁ V) (pullSec L π V s) j _ (inf_le_inf_left _ (congrFun hU j).ge) le_rfl
  rw [resG_self] at h
  refine h.trans ?_
  rw [coord_map, coord_pullSec, coord_powSec, map_pow, map_pow, resG_appLE]
  exact (resG_appLE π _ _ _).trans (hpow _ _ _ _ _)

include hpre hpow in

theorem nonempty_pullback_cokernel_pow (hL : L.IsLB) (hM : M.IsLB) (φ : toMod L ⟶ toMod M) :
    Nonempty ((Scheme.Modules.pullback ι).obj (cokernel (powHom n hL φ)) ≅
      (Scheme.Modules.pullback π).obj (cokernel φ)) := by
  obtain ⟨eL, hL'⟩ := exists_iso_pull n hpre hpow L
  obtain ⟨eM, hM'⟩ := exists_iso_pull n hpre hpow M
  have nat : pullMap hL hM π φ ≫ eM.hom =
      eL.hom ≫ pullMap (isLB_pwN n hL) (isLB_pwN n hM) ι (powHom n hL φ) := by
    refine (bijective_toPushforward_comp hL π _).1 ?_
    ext V s
    change eM.hom.app (π ⁻¹ᵁ V) ((pullMap hL hM π φ).app (π ⁻¹ᵁ V) (pullSec L π V s)) =
      (pullMap (isLB_pwN n hL) (isLB_pwN n hM) ι (powHom n hL φ)).app (π ⁻¹ᵁ V)
        (eL.hom.app (π ⁻¹ᵁ V) (pullSec L π V s))
    rw [pullMap_app_pullSec, hM', hL', app_modRes, pullMap_app_pullSec, powHom_app_powSec]
  have e₁ : (Scheme.Modules.pullback π).obj (cokernel φ) ≅ cokernel (pullMap hL hM π φ) :=
    PreservesCokernel.iso (Scheme.Modules.pullback π) _ ≪≫
      cokernel.mapIso _ _ (pullbackIso hL π) (pullbackIso hM π) (by rw [pullMap, Iso.hom_inv_id_assoc])
  have e₂ : (Scheme.Modules.pullback ι).obj (cokernel (powHom n hL φ)) ≅
      cokernel (pullMap (isLB_pwN n hL) (isLB_pwN n hM) ι (powHom n hL φ)) :=
    PreservesCokernel.iso (Scheme.Modules.pullback ι) _ ≪≫
      cokernel.mapIso _ _ (pullbackIso (isLB_pwN n hL) ι) (pullbackIso (isLB_pwN n hM) ι)
        (by rw [pullMap, Iso.hom_inv_id_assoc])
  exact ⟨e₂ ≪≫ (cokernel.mapIso _ _ eL eM nat).symm ≪≫ e₁.symm⟩

end Pull

end GlobalTheory.FrobPow

namespace GlobalTheory.FrobFilt

open GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobPow

theorem isFrob_cokernel_powHom {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] {B : GlobalTheory.Vert.Model O} {L M : LB B.X} (hL : L.IsLB) (hM : M.IsLB)
    (ψ : toMod L ⟶ toMod M) (φ : toMod M ⟶ toMod L) {g : Γ(B.X, ⊤)} (hg : IsRootOfP p g p)
    (h : φ ≫ ψ = smulHom _ g) : IsFrob p (cokernel ψ) (cokernel (powHom p hL ψ)) := by
  have hp := FrobQuot.natCast_eq_zero_fibI p B
  refine ⟨hp, ?_⟩
  have hC : smulHom (cokernel (powHom p hL ψ)) (g ^ p) = 0 :=
    (cancel_epi (cokernel.π _)).1 (by
      rw [comp_zero, ← smulHom_comp, ← powHom_comp p hM hL φ ψ g h, Category.assoc,
        cokernel.condition, comp_zero])
  have hCp : smulHom (cokernel (powHom p hL ψ)) (p : Γ(B.X, ⊤)) = 0 := by
    obtain ⟨u, hu⟩ := hg
    have e : (p : Γ(B.X, ⊤)) = (u⁻¹).val * g ^ p := by rw [hu, Units.inv_mul_cancel_left]
    rw [e, smulHom_mul, hC, zero_comp]
  haveI := isQuasicoherent_toMod (isLB_pwN p hL)
  haveI := isQuasicoherent_toMod (isLB_pwN p hM)
  have hI := FrobQuot.isIso_unit_fibI p B (cokernel (powHom p hL ψ)) hCp
  obtain ⟨e₃⟩ := nonempty_pullback_cokernel_pow p
    (π := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp ≫ (fibI p B).subschemeι)
    (ι := (fibI p B).subschemeι) (fun _ => rfl) (fun U W e e' a => by
      rw [← Scheme.Hom.appLE_comp_appLE (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp)
        (fibI p B).subschemeι U W W e' le_rfl, CommRingCat.hom_comp, RingHom.comp_apply]
      exact (GlobalTheory.SS.FrobField.absFrob_appLE _ p 1 Fact.out hp W le_rfl _).trans (by rw [pow_one]))
    hL hM ψ
  have e₄ := @asIso _ _ _ _ ((Scheme.Modules.pullbackPushforwardAdjunction
    (fibI p B).subschemeι).unit.app (cokernel (powHom p hL ψ))) hI
  exact ⟨e₄ ≪≫ (Scheme.Modules.pushforward (fibI p B).subschemeι).mapIso e₃⟩

theorem exists_pres_isFrob_of_rank_one : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]
    (B : GlobalTheory.Vert.Model O), ∀ (g : Γ(B.X, ⊤)), IsRootOfP p g p → ∀ R : Pres B, R.r = 1 →
    Kills g R.mod → ∃ R' : Pres B, IsFrob p R.mod R'.mod := by
  intro O _ _ _ p _ _ _ B g hg R hr hk
  have hmono := Pres.mono_ψ O B R
  obtain ⟨r, E, E', vb, vb', ψ, iso⟩ := R
  obtain rfl : r = 1 := hr
  have hM := vb.isLB_det
  have hL := vb'.isLB_det
  let ψ₀ : toMod (VB.det E' 1) ⟶ toMod (VB.det E 1) := vb'.isoDet.inv ≫ ψ ≫ vb.isoDet.hom
  haveI : Mono ψ := hmono
  haveI : Mono ψ₀ := inferInstance
  have e : cokernel ψ ≅ cokernel ψ₀ :=
    cokernel.mapIso _ _ vb'.isoDet vb.isoDet (by rw [Iso.hom_inv_id_assoc])
  have hk₀ : smulHom (cokernel ψ₀) g = 0 := kills_of_iso hk e
  let φ : toMod (VB.det E 1) ⟶ toMod (VB.det E' 1) :=
    Abelian.monoLift ψ₀ (smulHom _ g) (by rw [smulHom_comp, hk₀, comp_zero])
  have h₁ : φ ≫ ψ₀ = smulHom _ g := Abelian.monoLift_comp _ _ _
  have h₂ : ψ₀ ≫ φ = smulHom _ g := by
    rw [← cancel_mono ψ₀, Category.assoc, h₁, smulHom_comp]
  have hroot : IsRootOfP p (g ^ p) 1 := by
    obtain ⟨u, hu⟩ := hg
    exact ⟨u, by rw [pow_one, hu]⟩
  have i₁ := FlagRoot.isIso_genRes_smulHom one_pos hroot (toMod (pwN (VB.det E 1) p))
  have i₂ := FlagRoot.isIso_genRes_smulHom one_pos hroot (toMod (pwN (VB.det E' 1) p))
  rw [← powHom_comp p hM hL φ ψ₀ g h₁, Functor.map_comp] at i₁
  rw [← powHom_comp p hL hM ψ₀ φ g h₂, Functor.map_comp] at i₂
  haveI : Epi (B.genRes.map (powHom p hL ψ₀)) := epi_of_epi (B.genRes.map (powHom p hM φ)) _
  haveI : Mono (B.genRes.map (powHom p hL ψ₀)) := mono_of_mono _ (B.genRes.map (powHom p hM φ))
  refine ⟨⟨1, _, _, VB.isVB_toMod (isLB_pwN p hM), VB.isVB_toMod (isLB_pwN p hL),
    powHom p hL ψ₀, isIso_of_mono_of_epi _⟩, ?_⟩
  obtain ⟨f⟩ := isFrob_iff.1 (isFrob_cokernel_powHom p hL hM ψ₀ φ hg h₁)
  exact isFrob_iff.2 ⟨f ≪≫ (frob p B).mapIso e.symm⟩

end GlobalTheory.FrobFilt
