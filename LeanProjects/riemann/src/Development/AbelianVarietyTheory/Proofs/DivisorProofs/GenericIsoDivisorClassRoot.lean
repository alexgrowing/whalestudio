import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullback
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vert.RootDiv

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : Vert.Model O}

theorem isIso_of_isUnit (E : Z.X.Modules) {s : Γ(Z.X, ⊤)}
    (h : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom s)) : IsIso (Z.genRes.map (smulHom E s)) := by
  rw [VB.pullback_map_smulHom]
  exact (isUnit_iff_isIso _).1 (h.map (smulEnd _))

theorem genIso_ext {E E' : Z.X.Modules} {φ ψ : Z.GenIso E E'} (h : φ.inv = ψ.inv) : φ = ψ :=
  Iso.ext ((Iso.inv_eq_inv _ _).1 h)

def mul (E : Z.X.Modules) (s : Γ(Z.X, ⊤)) (h : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom s)) :
    Z.GenIso E E :=
  haveI := isIso_of_isUnit E h
  Vert.Model.GenIso.ofHom (smulHom E s)

theorem mul_inv_eq (E : Z.X.Modules) (s : Γ(Z.X, ⊤)) (h : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom s)) :
    (mul E s h).inv = Z.genRes.map (smulHom E s) := rfl

variable {r : ℕ} {E : Z.X.Modules} (hE : GlobalTheory.VB.IsVB E r)

theorem cls_mul_mul (s t : Γ(Z.X, ⊤)) (hs : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom s))
    (ht : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom t))
    (hst : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (s * t))) :
    (Vert.Model.GenIso.div (mul E (s * t) hst) hE hE).cls =
      (Vert.Model.GenIso.div (mul E s hs) hE hE).cls + (Vert.Model.GenIso.div (mul E t ht) hE hE).cls := by
  have : mul E (s * t) hst = mul E s hs ≪≫ mul E t ht := genIso_ext (by
    rw [Iso.trans_inv, mul_inv_eq, mul_inv_eq, mul_inv_eq, ← Functor.map_comp, smulHom_mul])
  rw [this]
  exact Vert.Model.GenIso.cls_div_trans _ hE hE hE _

theorem cls_mul_unit (u : Γ(Z.X, ⊤)ˣ) (h : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (u : Γ(Z.X, ⊤)))) :
    (Vert.Model.GenIso.div (mul E u h) hE hE).cls = 0 := by
  let β : E ≅ E := ⟨smulHom E ((u⁻¹ : Γ(Z.X, ⊤)ˣ) : Γ(Z.X, ⊤)), smulHom E u,
    by rw [← smulHom_mul, Units.mul_inv, smulHom_one],
    by rw [← smulHom_mul, Units.inv_mul, smulHom_one]⟩
  have : mul E u h = Z.genRes.mapIso β := genIso_ext rfl
  rw [this]
  exact GlobalTheory.Vert.FlagPairPull.cls_div_mapIso β hE hE

theorem cls_mul_pow (s : Γ(Z.X, ⊤)) (hs : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom s)) (n : ℕ)
    (hn : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (s ^ n))) :
    (Vert.Model.GenIso.div (mul E (s ^ n) hn) hE hE).cls =
      n • (Vert.Model.GenIso.div (mul E s hs) hE hE).cls := by
  induction n with
  | zero =>
    have : mul E (s ^ 0) hn = Z.genRes.mapIso (Iso.refl E) :=
      genIso_ext (by rw [mul_inv_eq, pow_zero, smulHom_one]; rfl)
    rw [this, GlobalTheory.Vert.FlagPairPull.cls_div_mapIso, zero_smul]
  | succ n ih =>
    have hn' : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (s ^ n)) := by
      rw [map_pow]; exact hs.pow n
    have e1 : mul E (s ^ (n + 1)) hn = mul E (s ^ n * s) (by rw [← pow_succ]; exact hn) := by
      exact genIso_ext (by rw [mul_inv_eq, mul_inv_eq, pow_succ])
    rw [e1, cls_mul_mul hE _ _ hn' hs, ih hn', succ_nsmul]

theorem isUnit_of_root (p : ℕ) [Fact p.Prime] [CharZero O] {g : Γ(Z.X, ⊤)} {a : ℕ} (ha : 0 < a)
    (h : IsRootOfP p g a) : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom g) := by
  have hp : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (Z.const (p : O))) :=
    RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x _ => (Scheme.mem_basicOpen_top _ _ x).1
      ((Scheme.preimage_basicOpen_top Z.gen.ι _).le (Z.gen_le_basicOpen (natCast_ne_zero O p) x.2))
  obtain ⟨u, hu⟩ := h
  rw [show Z.const (p : O) = (p : Γ(Z.X, ⊤)) from map_natCast _ p] at hp
  have hpow : IsUnit (((Scheme.Hom.appTop Z.gen.ι).hom g) ^ a) := by
    rw [← map_pow, hu, map_mul]
    exact (u.isUnit.map _).mul hp
  exact (isUnit_pow_iff ha.ne').1 hpow

end GlobalTheory.Vert.RootDiv

open GlobalTheory.Vert.RootDiv in

theorem GlobalTheory.Vert.Model.GenIso.nsmul_cls_div_of_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (Z : GlobalTheory.Vert.Model O) (L L' : Z.X.Modules) (r : ℕ) (hL : GlobalTheory.VB.IsVB L r) (hL' : GlobalTheory.VB.IsVB L' r) (φ : Z.GenIso L L') (e : L' ≅ L) (g : Γ(Z.X, ⊤)) (a : ℕ), 0 < a → IsRootOfP p g a → φ.inv = Z.genRes.map (e.hom ≫ smulHom L g) → a • (GlobalTheory.Vert.Model.GenIso.div φ hL hL').cls = r • Z.divP p := by
  intro O _ _ _ p _ _ _ Z L L' r hL hL' φ e g a ha hroot hφ
  have hg := isUnit_of_root (Z := Z) p ha hroot
  have hroot' := hroot
  obtain ⟨u, hu⟩ := hroot'
  have hga : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (g ^ a)) := by
    rw [map_pow]; exact hg.pow a
  have hu' : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (u : Γ(Z.X, ⊤))) := u.isUnit.map _
  have hp : IsUnit ((Scheme.Hom.appTop Z.gen.ι).hom (p : Γ(Z.X, ⊤))) := by
    have := (isUnit_of_root (Z := Z) p ha hroot).pow a
    rw [← map_pow, hu, map_mul] at this
    exact isUnit_of_mul_isUnit_right this
  have hsplit : φ = mul L g hg ≪≫ Z.genRes.mapIso e.symm := genIso_ext (by
    rw [Iso.trans_inv, hφ, mul_inv_eq, Functor.mapIso_inv, Iso.symm_inv, Functor.map_comp])
  have hup : mul L (g ^ a) hga = mul L ((u : Γ(Z.X, ⊤)) * (p : Γ(Z.X, ⊤))) (by rw [← hu]; exact hga) :=
    genIso_ext (by rw [mul_inv_eq, mul_inv_eq, hu])
  have hP : (Vert.Model.GenIso.div (mul L (p : Γ(Z.X, ⊤)) hp) hL hL).cls = r • Z.divP p :=
    Vert.Model.GenIso.cls_div_of_smul hL (natCast_ne_zero O p) (by rw [mul_inv_eq, show Z.const (p : O) = (p : Γ(Z.X, ⊤)) from map_natCast _ p])
  rw [hsplit, Vert.Model.GenIso.cls_div_trans _ hL hL hL', GlobalTheory.Vert.FlagPairPull.cls_div_mapIso,
    add_zero, ← cls_mul_pow hL g hg a hga, hup, cls_mul_mul hL _ _ hu' hp, cls_mul_unit hL u hu',
    zero_add, hP]
