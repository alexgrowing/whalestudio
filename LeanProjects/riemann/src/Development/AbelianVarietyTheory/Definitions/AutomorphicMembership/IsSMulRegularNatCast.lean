import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem eq_zero_of_flat {R T : Type} [CommRing R] [IsDomain R] [CharZero R] [CommRing T] (φ : R →+* T) (hφ : φ.Flat)
    {c : ℕ} (hc : c ≠ 0) {a : T} (h : (c : T) * a = 0) : a = 0 := by
  let := φ.toAlgebra
  have : Module.Flat R T := hφ
  have hr :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (R := R) (M := T) (r := (c : R)) (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hc))
  refine hr (a₁ := a) (a₂ := 0) ?_
  simp only [Nat.cast_smul_eq_nsmul, smul_zero, nsmul_eq_mul, h]

def Lat.mulIncl {B : Mdl Y i₀} (L : Lat B) (c : ℕ) : L.N.toMod ⟶ B.om :=
  LB.homOfLinear (fun V => c • QCoh.appLinear L.N.incl V) fun h s =>
    (congrArg (c • ·) (Twist.app_resM L.N.incl h s)).trans (map_nsmul (Twist.resM B.om h) c _).symm

theorem Mdl.isSMulRegular_natCast (B : Mdl Y i₀) {U : B.X.Opens} (hU : IsAffineOpen U) {c : ℕ} (hc : c ≠ 0)
    {a : Γ(B.X, U)} (h : (c : Γ(B.X, U)) * a = 0) : a = 0 := by
  have := B.flat
  have hf := Flat.flat_appLE B.s (isAffineOpen_top _) hU le_top
  let φ : B.i.c.V W →+* Γ(B.X, U) := (B.s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of (B.i.c.V W))).inv.hom
  have hφ : φ.Flat := (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (B.i.c.V W))).inv)).comp hf
  exact eq_zero_of_flat φ hφ hc h

def Lat.powSMul {B : Mdl Y i₀} (hp : p ≠ 0) (L : Lat B) (c : ℕ) : Lat B :=
  have : Mono (L.mulIncl (p ^ c)) := QCoh.mono_of_locally_app_injective _ fun V x hx => by
    obtain ⟨V', n, m, hx', hm⟩ := L.free x
    obtain ⟨U, hU, hxU, hle⟩ := QCoh.exists_affine_mem_le (U := V ⊓ V') x ⟨hx, hx'⟩
    refine ⟨U, hxU, hle.trans inf_le_left, (injective_iff_map_eq_zero _).2 fun s hs => ?_⟩
    have h₁ : ((p ^ c : ℕ) : Γ(B.X, U)) • s = 0 := L.N.incl_app_injective U (by
      rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_zero]
      exact hs)
    let b := hm.basis (hle.trans inf_le_right)
    refine b.ext_elem fun i => B.isSMulRegular_natCast hU (pow_ne_zero c hp) ?_ |>.trans (by simp)
    simpa using congrArg (fun z => b.repr z i) h₁
  Lat.ofBundle (L.mulIncl (p ^ c)) L.free fun V hV s => by
    have hu : IsUnit ((p : ℕ) : Γ(B.X, V)) := by
      have := (B.X.toRingedSpace.isUnit_res_basicOpen ((p : ℕ) : Γ(B.X, ⊤))).map
        (B.X.presheaf.map (homOfLE hV).op).hom
      exact (map_natCast ((B.X.presheaf.map (homOfLE hV).op).hom.comp
        (B.X.presheaf.map (homOfLE (B.X.basicOpen_le _)).op).hom) p) ▸ this
    obtain ⟨u, hu⟩ := hu.pow c
    obtain ⟨r, hr⟩ := L.N.mem_sec_iff.1 ((L.gen V hV).ge (Submodule.mem_top (x := (↑u⁻¹ : Γ(B.X, V)) • s)))
    refine ⟨r, ?_⟩
    change p ^ c • L.N.incl.app V r = s
    rw [hr, ← Nat.cast_smul_eq_nsmul Γ(B.X, V), Nat.cast_pow, ← hu, smul_smul, Units.mul_inv, one_smul]

end GlobalTheory.LocM
