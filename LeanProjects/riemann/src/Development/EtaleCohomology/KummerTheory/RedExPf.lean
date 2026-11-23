import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedExPf
open LateralTheory.KummerTheory.BockCut

theorem nsmul_congr {q : ℕ} {i : ℤ} {U : Scheme.{0}} (y : Sec (tw q i) U) {n m : ℕ}
    (h : (n : ZMod q) = (m : ZMod q)) : n • y = m • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) n y, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) m y]
  congr 1
  exact ULift.ext _ _ (by simpa using h)

theorem RedEx_of (hZ : ZHom) (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) : RedEx := by
  intro Q q _ h i
  have hq : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) h⟩
  choose ρ hρ using fun (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) => (hP Q Γ(U, ⊤)).2.2.2.2.2 q h ζ
  let M : Shv (ZMod Q) := (restr (ZMod.castHom h (ZMod q))).obj (tw q i)
  let e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U := fun U ζ => (twGen i (ρ U ζ) : Sec (tw q i) U)
  have he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    have hx : ρ V (ζ.map g.appTop.hom) = (ρ U ζ).map g.appTop.hom := by
      apply Subtype.ext
      rw [hρ]
      show (g.appTop.hom ζ.1) ^ (Q / q) = g.appTop.hom ((ρ U ζ).1)
      rw [hρ, map_pow]
    show Sec.res (F := tw q i) g (twGen i (ρ U ζ)) = twGen i (ρ V (ζ.map g.appTop.hom))
    rw [hx, (hT q i).2.2.2.1]
  have he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ := by
    intro U ζ ξ a hξa
    let b : (ZMod q)ˣ := ZMod.unitsMap h a
    have hb : ∀ x : ZMod Q, ((ZMod.castHom h (ZMod q) x : ZMod q)) = (x.val : ZMod q) := fun x =>
      ZMod.cast_eq_val x
    have hpow : (ρ U ξ).1 = (ρ U ζ).1 ^ (b : ZMod q).val := by
      have h1 : (ρ U ζ).1 ^ q = 1 := (hP q Γ(U, ⊤)).1 (ρ U ζ)
      have hbv : (b : ZMod q).val = (a : ZMod Q).val % q := by
        show (ZMod.castHom h (ZMod q) (a : ZMod Q)).val = _
        rw [hb, ZMod.val_natCast]
      rw [hρ, hρ, hξa, hbv, ← pow_mul, mul_comm, pow_mul]
      conv_lhs => rw [← Nat.div_add_mod (a : ZMod Q).val q]
      rw [hρ] at h1
      rw [pow_add, pow_mul, h1, one_pow, one_mul]
    show twGen i (ρ U ξ) = _ • (twGen i (ρ U ζ) : Sec (tw q i) U)
    rw [(hT q i).2.2.2.2.1 U (ρ U ζ) (ρ U ξ) b hpow]
    apply nsmul_congr
    rw [ZMod.natCast_zmod_val]
    have : ((b ^ i : (ZMod q)ˣ) : ZMod q) = ZMod.castHom h (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q) := by
      rw [show b ^ i = ZMod.unitsMap h (a ^ i) from (map_zpow _ _ _).symm]
      rfl
    rw [this, hb]
  obtain ⟨φ, hφ, -⟩ := (hT Q i).2.2.2.2.2 M e he1 he2
  obtain ⟨π, hπ⟩ := hZ (TZ Q i) (TZ q i)
    (fun U => AddMonoidHom.mk' (fun a => (Sec.map φ (show Sec (tw Q i) U from a) : Sec (tw q i) U))
      (fun a b => map_add (φ.hom.app (op U)).hom a b))
    (fun V U g a => by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) a
      exact this.symm)
  refine ⟨π, fun U ζ ξ hξ => ?_⟩
  rw [hπ]
  have hx : ξ = ρ U ζ := Subtype.ext (by rw [hξ, hρ])
  subst hx
  exact hφ U ζ

end LateralTheory.KummerTheory.RedExPf
