import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PerpTorus
open GlobalTheory.ZH.TorusPerp GlobalTheory.TorusExt

theorem exists_form {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) {X : Type} [AddCommGroup X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (a : S.Gam) (ha : a ∈ S.perp yy.ker) :
    ∃ m : X →+ ZMod (S.r * S.N), ∀ b α, yy b = QuotientAddGroup.mk α → m α = eStd S.g _ a b := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ b b' : S.Gam, yy b = yy b' → eStd S.g _ a b = eStd S.g _ a b' := by
    intro b b' e
    have h0 : eStd S.g _ a (b - b') = 0 := ha _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  refine ⟨AddMonoidHom.mk' (fun α => eStd S.g _ a (σ α)) fun α β => ?_, fun b α e => ind _ _ ((hσ α).trans e.symm)⟩
  rw [← eStd_add_right]
  exact ind _ _ (by rw [map_add, hσ, hσ, hσ, QuotientAddGroup.mk_add])

attribute [local instance] gtGroup in

theorem exists_torus_point : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (g : u.Geom) (a : S.Gam) (ha : a ∈ S.perp l.yy.ker), ∃ (q : QkPt u.D.toPre (PadicAlgCl p) S.N) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (g.pt (S.r • a)) ∧ ∀ χ, (τ (Multiplicative.ofAdd χ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζN ^ (l.wt χ ⟨a, ha⟩).val)) := by
  intro hL hT o Ω _ _ _ hA S ρ p _ y₀ u l g a ha
  have hG := hL.1.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hadm : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let ω : (PadicAlgCl p)ˣ := Units.map (y₀.comp (algebraMap o S.R)).toMonoidHom (hζ.isUnit hn.ne).unit
  have hωv : (ω : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N))) := rfl
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map

  let pt : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    MonoidHom.mk' (fun a => g.pt a.toAdd) fun _ _ => g.pt_add _ _
  have pt_nsmul : ∀ (n : ℕ) b, g.pt (n • b) = g.pt b ^ n := fun n b => map_pow pt (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q, f q = g.pt b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul]
    exact map_one pt)
  obtain ⟨m, hm⟩ := exists_form S l.yy l.yy_onto a ha
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
    (AddChar.zmodChar (S.r * S.N) hω.pow_eq_one).toMonoidHom.comp m.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (m α).val := fun _ => rfl
  have hτ1 : τ ^ (S.r * S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (m α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow]
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) hB τ hτ1
  obtain ⟨q₁, hq₁, hq₁τ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.N) hB (τ ^ S.r) (by rw [← pow_mul, hτ1])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a', ha', -⟩ := g.pt_bij (f q) hq1
  have haa : a' = a := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)
    rw [← ha', hq'] at w₁
    have w₂ := g.weil a' b (ω ^ (eStd S.g _ a' b).val) (by
      rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul])
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB w₂ w₁)
    rw [hτ] at e₁
    have e₂ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)
    rw [hm b _ (l.yy_eq b q' _ ((f₁ _ _).2 hq'.symm) (g.pt_over b))] at e₂
    have e₃ := eStd_add_left S.g _ (a' - a) a b
    rw [sub_add_cancel, e₂] at e₃
    exact left_eq_add.1 (e₃.trans (add_comm _ _))
  subst haa
  refine ⟨q₁, τ ^ S.r, hq₁, hq₁τ, ?_, fun χ => ?_⟩
  · rw [pt_nsmul]
    refine (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) (by omega) hr
      (mul_comm _ _) q₁ q _).2 (hq₁.trans hq.symm) ((isNsmul_iff_eq _ _ _).2 ?_) ((f₁ _ _).2 ha')
    rw [(isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hq₁τ), (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hqτ),
      ofMul_pow, map_nsmul]
  · obtain ⟨b, hb⟩ := l.yy_onto (QuotientAddGroup.mk χ)
    have z : S.ζN ^ S.N = 1 := by
      rw [ThetaSys.ζN, ← pow_mul, ← S.prim.pow_eq_one]
      congr 1
      ring
    have z' : S.ζN = (S.ζ ^ (S.r * S.N)) ^ S.r := by
      rw [ThetaSys.ζN, ← pow_mul]
      congr 1
      ring
    rw [l.wt_eq b χ hb, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ z,
      MonoidHom.pow_apply, hτ, hm b χ hb, z', pow_right_comm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hωv,
      ← map_pow, ← map_pow, ← map_pow, ← map_pow]

end GlobalTheory.ZH.PerpTorus
end
