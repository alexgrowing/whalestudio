import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElement

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison

namespace Wc

def basePt {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂}
    (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) : F.ptK κ₂ ⟶ F.ptK κ₁ where
  app B₀ := TypeCat.ofHom fun z => ⟨(z.1.1.comp τ, z.1.2), by rw [RingHom.comp_assoc, h]; exact z.2⟩
  naturality _ _ _ := rfl

noncomputable def frb {l : ℕ} [Fact l.Prime] {B₀ : Type} [CommRing B₀] (h : (l : B₀) = 0) : B₀ →+* B₀ :=
  _root_.UpperTheory.Reformulated.B.FrobeniusElement.frb h

theorem idc {Λ S : Type} [CommRing Λ] [CommRing S] (c : Λ →+* S) (a : Λ) : RingHom.id S (c a) = c (RingHom.id Λ a) := rfl

theorem cast_zero {l : ℕ} {k₀ B₀ : Type} [CommRing k₀] [CommRing B₀] (h : (l : k₀) = 0) (ψ : k₀ →+* B₀) : (l : B₀) = 0 := by
  rw [← map_natCast ψ, h, map_zero]

theorem frb_nat {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : B.Fn O) {B₀ B' : CommRingCat.{0}} (φ : B₀ ⟶ B') (h : (l : B₀) = 0)
    (h' : (l : B') = 0) (y : F.Pt.obj B₀) :
    F.Pt.map (CommRingCat.ofHom (frb h')) (F.Pt.map φ y) = F.Pt.map φ (F.Pt.map (CommRingCat.ofHom (frb h)) y) := by
  have e : φ ≫ CommRingCat.ofHom (frb h') = CommRingCat.ofHom (frb h) ≫ φ :=
    CommRingCat.hom_ext (RingHom.ext fun x => (map_pow φ.hom x l).symm)
  exact (F.Pt.map_comp_apply φ (CommRingCat.ofHom (frb h')) y).symm.trans
    ((congrArg (fun t : B₀ ⟶ B' => F.Pt.map t y) e).trans (F.Pt.map_comp_apply (CommRingCat.ofHom (frb h)) φ y))

def frbPt {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : B.Fn O) {k₀ : Type} [CommRing k₀] (κ : O →+* k₀) (h : (l : k₀) = 0) :
    F.ptK κ ⟶ F.ptK κ where
  app B₀ := TypeCat.ofHom fun z => (F.ptK κ).map (CommRingCat.ofHom (frb (cast_zero h z.1.1))) z
  naturality B₀ B' φ := by
    ext z
    exact Subtype.ext (Prod.ext (RingHom.ext fun x => (map_pow φ.hom _ l).symm)
      (frb_nat F φ (cast_zero h z.1.1) (cast_zero h (φ.hom.comp z.1.1)) z.1.2))

theorem base_frb {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁}
    {κ₂ : O →+* k₂} (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) (h₁ : (l : k₁) = 0) (h₂ : (l : k₂) = 0) (B₀ : CommRingCat.{0})
    (y : (F.ptK κ₂).obj B₀) :
    ((frbPt F κ₁ h₁).app B₀ ((basePt F τ h).app B₀ y)).1.2 = ((basePt F τ h).app B₀ ((frbPt F κ₂ h₂).app B₀ y)).1.2 := rfl

theorem base_map {O : Type} [CommRing O] {F F' : B.Fn O} (u : B.Fn.Map F F') {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁}
    {κ₂ : O →+* k₂} (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) :
    ((u.ptK κ₁).app B₀ ((basePt F τ h).app B₀ y)).1.2 = ((basePt F' τ h).app B₀ ((u.ptK κ₂).app B₀ y)).1.2 := rfl

variable (l : ℕ) [hl : Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l]

abbrev Wm (m : ℕ) : Type := WittVector l k ⧸ Ideal.span {(l : WittVector l k) ^ m}

abbrev Im (m : ℕ) : Ideal (Wm l k m) := (Ideal.span {(l : WittVector l k)}).map (Ideal.Quotient.mk _)

def pd (m : ℕ) : DividedPowers (Im l k m) := (exists_pd_l l (witt_unit l k) (witt_tf l k) m).choose

theorem isPd (m : ℕ) : R.IsPd (Ideal.Quotient.mk _) (Ideal.span {(l : WittVector l k)}) (pd l k m) :=
  (exists_pd_l l (witt_unit l k) (witt_tf l k) m).choose_spec

abbrev bs (m : ℕ) : Base where
  R := Wm l k m
  I := Im l k m
  γ := pd l k m
  t := 1
  p := l

def res (m : ℕ) : k →+* Wm l k m ⧸ Im l k m :=
  (WittVector.constantCoeff (p := l) (R := k)).liftOfSurjective (WittVector.constantCoeff_surjective l)
    ⟨(Ideal.Quotient.mk _).comp (Ideal.Quotient.mk _), fun x hx => Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_map_of_mem _ ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).2 hx))⟩

theorem res_coeff (m : ℕ) (x : WittVector l k) :
    res l k m (WittVector.constantCoeff x) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

def red (m : ℕ) : Wm l k (m + 1) →+* Wm l k m :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ m.le_succ))

omit [CharP k l] [PerfectRing k l] in
theorem red_mk (m : ℕ) (x : WittVector l k) : red l k m (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (RingHom.id _ x) :=
  Ideal.Quotient.factor_mk _ x

theorem dp_red (m : ℕ) : IsDPMorphism (pd l k (m + 1)) (pd l k m) (red l k m) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id _) _ Ideal.Quotient.mk_surjective (pdI_l l (witt_unit l k)) (isPd l k _) (isPd l k _)
    (fun _ hx => hx) fun _ => rfl

def frob (m : ℕ) : Wm l k m →+* Wm l k m :=
  Ideal.quotientMap _ WittVector.frobenius (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
    exact Ideal.mem_span_singleton_self _)

omit [CharP k l] [PerfectRing k l] in
theorem frob_mk' (m : ℕ) (x : WittVector l k) : frob l k m (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (WittVector.frobenius x) :=
  Ideal.quotientMap_mk

omit [CharP k l] [PerfectRing k l] in
theorem red_frob (m : ℕ) (r : Wm l k (m + 1)) : red l k m (frob l k (m + 1) r) = frob l k m (red l k m r) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [frob_mk', red_mk, red_mk, frob_mk', RingHom.id_apply, RingHom.id_apply]

theorem dp_frob (m : ℕ) : IsDPMorphism (pd l k m) (pd l k m) (frob l k m) :=
  RL.pd_mor _ _ _ _ _ _ WittVector.frobenius _ Ideal.Quotient.mk_surjective (pdI_l l (witt_unit l k)) (isPd l k _) (isPd l k _)
    (fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) fun _ => rfl

theorem frob_mk (m : ℕ) (r : Wm l k m) : Ideal.Quotient.mk (Im l k m) (frob l k m r) = Ideal.Quotient.mk (Im l k m) r ^ l := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (WittVector.frobenius x)) = _
  rw [← res_coeff, ← res_coeff, ← map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.coeff_frobenius_charP]

variable {k} {O : Type} [CommRing O] (F : B.Fn O) (ρ : O →+* k)

abbrev L (m : ℕ) : (bs l k m).Fun := F.cr (bs l k m) rfl ((res l k m).comp ρ)

abbrev OA (m : ℕ) : Thick (L l F ρ m) ⥤ CommAlgCat.{0} (WittVector l k) := B.OA (L l F ρ m) (Ideal.Quotient.mk _)

abbrev OM (m : ℕ) : Thick (L l F ρ m) ⥤ ModuleCat.{0} (WittVector l k) := B.OM (L l F ρ m) (Ideal.Quotient.mk _)

theorem red_res (m : ℕ) : (Ideal.quotientMap _ (red l k m) (Ideal.map_le_iff_le_comap.1 (dp_red l k m).1)).comp
    ((res l k (m + 1)).comp ρ) = (res l k m).comp ρ := RingHom.ext fun x => by
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective l (ρ x)
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← hw, res_coeff, res_coeff]; rfl

def redM (m : ℕ) : Mor (L l F ρ (m + 1)) (L l F ρ m) (red l k m) :=
  B.crMor (F := F) (F' := F) (b := bs l k (m + 1)) (b' := bs l k m) (ht := rfl) (ht' := rfl) (red l k m) rfl (dp_red l k m)
    (basePt F _ (red_res l ρ m)) fun _ _ _ => rfl

def redMor (m : ℕ) : CH.Mor (OM l F ρ (m + 1)) (OM l F ρ m) (RingHom.id _) := B.omMor (redM l F ρ m) (RingHom.id _) (red_mk l k m)

def HS (j : ℕ) : Sys.{1} (WittVector l k) where
  M m := CH.H (OM l F ρ m) j
  r m := (redMor l F ρ m).pull j

omit [PerfectRing k l] [CharP k l] in
variable (k) in
theorem l_zero (m : ℕ) : (l : Wm l k m ⧸ Im l k m) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), ← map_natCast (Ideal.Quotient.mk _)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))

def phiM (m : ℕ) : Mor (L l F ρ m) (L l F ρ m) (frob l k m) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k m) (ht := rfl) (ht' := rfl) (frob l k m) rfl (dp_frob l k m)
    (frbPt F _ (l_zero l k m)) fun _ y r => ((congrArg y.1.1 (frob_mk l k m r)).trans (map_pow y.1.1 _ l)).symm

def phiMor (m : ℕ) : CH.Mor (OM l F ρ m) (OM l F ρ m) WittVector.frobenius :=
  B.omMor (phiM l F ρ m) WittVector.frobenius (frob_mk' l k m)

theorem red_phi (m j : ℕ) (x : CH.H (OM l F ρ (m + 1)) j) :
    (redMor l F ρ m).pull j ((phiMor l F ρ (m + 1)).pull j x) = (phiMor l F ρ m).pull j ((redMor l F ρ m).pull j x) := by
  unfold redMor phiMor
  exact cr_square (phiM l F ρ (m + 1)) (redM l F ρ m) (redM l F ρ m) (phiM l F ρ m) (frob_mk' l k _) (red_mk l k m) (red_mk l k m)
    (frob_mk' l k _) (red_frob l k m) (base_frb F _ (red_res l ρ m) (l_zero l k _) (l_zero l k _)) j x

def phiS (j : ℕ) : Sys.Hom (HS l F ρ j) (HS l F ρ j) WittVector.frobenius where
  f m := (phiMor l F ρ m).pull j
  comm m x := red_phi l F ρ m j x

variable {F} {F' : B.Fn O}

def pullM (u : B.Fn.Map F F') (m : ℕ) : Mor (L l F' ρ m) (L l F ρ m) (RingHom.id _) :=
  B.crMor (F := F') (F' := F) (b := bs l k m) (b' := bs l k m) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    (DPMorphism.id _).isDPMorphism (u.ptK _) fun _ _ _ => rfl

def pullMor (u : B.Fn.Map F F') (m : ℕ) : CH.Mor (OM l F' ρ m) (OM l F ρ m) (RingHom.id _) :=
  B.omMor (pullM l ρ u m) (RingHom.id _) (idc _)

theorem red_pull (u : B.Fn.Map F F') (m j : ℕ) (x : CH.H (OM l F' ρ (m + 1)) j) :
    (redMor l F ρ m).pull j ((pullMor l ρ u (m + 1)).pull j x) = (pullMor l ρ u m).pull j ((redMor l F' ρ m).pull j x) := by
  unfold redMor pullMor
  exact cr_square (pullM l ρ u (m + 1)) (redM l F ρ m) (redM l F' ρ m) (pullM l ρ u m) (idc _) (red_mk l k m) (red_mk l k m)
    (idc _) (fun r => (idc (red l k m) r).symm) (base_map u _ (red_res l ρ m)) j x

def pullS (u : B.Fn.Map F F') (j : ℕ) : Sys.Hom (HS l F' ρ j) (HS l F ρ j) (RingHom.id _) where
  f m := (pullMor l ρ u m).pull j
  comm m x := red_pull l ρ u m j x

variable (k) in

abbrev K₀ : Type := FractionRing (WittVector l k)

variable (k) in

def frob₀ : K₀ l k →ₛₗ[(WittVector.frobenius : WittVector l k →+* WittVector l k)] K₀ l k where
  toFun := WittVector.FractionRing.frobeniusRingHom l k
  map_add' := map_add _
  map_smul' a x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

variable (F) in

def D (j : ℕ) : Type 1 := K₀ l k ⊗[WittVector l k] (HS l F ρ j).lim

instance (j : ℕ) : AddCommGroup (D l F ρ j) := inferInstanceAs (AddCommGroup (K₀ l k ⊗[WittVector l k] (HS l F ρ j).lim))

instance (j : ℕ) : Module (K₀ l k) (D l F ρ j) := inferInstanceAs (Module (K₀ l k) (K₀ l k ⊗[WittVector l k] (HS l F ρ j).lim))

variable (F) in

def phiD (j : ℕ) : D l F ρ j →+ D l F ρ j := (TensorProduct.map (frob₀ l k) (phiS l F ρ j).lim).toAddMonoidHom

def pullD (u : B.Fn.Map F F') (j : ℕ) : D l F' ρ j →ₗ[K₀ l k] D l F ρ j := ((pullS l ρ u j).lim).baseChange (K₀ l k)

end Wc

end CrystallineSemistableComparison
