import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.ChainPts

namespace GlobalTheory.ChainPts.Forget

theorem exists_mul_of_pow {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {a b w : R} {n : ℕ}
    (hn : n ≠ 0) (h : b ^ n = w * a ^ n) : ∃ t, b = a * t := by
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, ?_⟩
    rw [zero_pow hn, mul_zero] at h
    rw [mul_zero]
    exact pow_eq_zero_iff hn |>.1 h
  · let K := FractionRing R
    have ha' : algebraMap R K a ≠ 0 := fun h0 => ha (IsFractionRing.injective R K (by rw [h0, map_zero]))
    set y : K := algebraMap R K b / algebraMap R K a with hydef
    have hy : y ^ n = algebraMap R K w := by
      rw [hydef, div_pow, ← map_pow, ← map_pow, h, map_mul, map_pow, mul_div_assoc, div_self (pow_ne_zero _ ha'),
        mul_one]
    have hint : IsIntegral R y := ⟨Polynomial.X ^ n - Polynomial.C w, Polynomial.monic_X_pow_sub_C w hn, by
      simp [hy]⟩
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨t, IsFractionRing.injective R K ?_⟩
    rw [map_mul, ht, hydef]
    rw [← mul_div_assoc]
    exact (mul_div_cancel_left₀ _ ha').symm

theorem exists_local_dvd {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] {a b w : Γ(X, ⊤)} {n : ℕ} (hn : n ≠ 0)
    (h : b ^ n = w * a ^ n) (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∃ c : Γ(V, ⊤), V.ι.appTop b = V.ι.appTop a * c := by
  let G := (X.presheaf.germ ⊤ x trivial).hom
  obtain ⟨t, ht⟩ := exists_mul_of_pow (R := X.presheaf.stalk x) (a := G a) (b := G b) (w := G w) hn
    (by rw [← map_pow, h, map_mul, map_pow])
  obtain ⟨U, hxU, s, hs⟩ := X.presheaf.germ_exist t
  obtain ⟨V, hxV, i₁, i₂, hV⟩ := X.presheaf.germ_eq x (show x ∈ (⊤ : X.Opens) from trivial) hxU b
    ((X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom a * s) (by
      rw [map_mul, hs]
      change G b = _
      rw [ht]
      congr 1
      exact (X.presheaf.germ_res_apply (homOfLE le_top : U ⟶ ⊤) x hxU a).symm)
  refine ⟨V, hxV, (X.presheaf.map (homOfLE (Scheme.Opens.ι_image_le V ⊤)).op).hom ((X.presheaf.map i₂.op).hom s), ?_⟩
  have := congrArg (X.presheaf.map (homOfLE (Scheme.Opens.ι_image_le V ⊤)).op).hom hV
  simp only [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp] at this
  rw [Scheme.Opens.ι_appTop]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact this

theorem kills_of_pow {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] {a b w : Γ(X, ⊤)} {n : ℕ} (hn : n ≠ 0)
    (h : b ^ n = w * a ^ n) {F : X.Modules} (hF : smulHom F a = 0) : smulHom F b = 0 := by
  refine LocFreeQuot.eq_zero_of_locally _ fun x => ?_
  obtain ⟨V, hx, c, hc⟩ := exists_local_dvd hn h x
  refine ⟨V, hx, ?_⟩
  rw [VB.pullback_map_smulHom, hc, smulHom_mul, ← VB.pullback_map_smulHom, hF, Functor.map_zero, comp_zero]

end GlobalTheory.ChainPts.Forget

namespace GlobalTheory.ChainPts.Forget

section Iso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime]
  {B : Vert.Model O} {Λ : Type} [CommRing Λ]

theorem kills_of_iso {g : Γ(B.X, ⊤)} {F G : B.X.Modules} (h : Kills g F) (e : F ≅ G) : Kills g G := by
  unfold Kills at h ⊢
  rw [← cancel_epi e.hom, ← smulHom_comp, h, zero_comp, comp_zero]

theorem isFrob_of_iso {F F' G G' : B.X.Modules} (h : IsFrob p F F') (e : F ≅ G) (e' : F' ≅ G') : IsFrob p G G' := by
  obtain ⟨hp, ⟨f⟩⟩ := h
  exact ⟨hp, ⟨e'.symm ≪≫ f ≪≫ (Scheme.Modules.pushforward _).mapIso ((Scheme.Modules.pullback _).mapIso e)⟩⟩

theorem isExt_of_isExtA {F₁ F₂ F₃ : AM B Λ} {G₁ G₂ G₃ : B.X.Modules} (h : IsExtA F₁ F₂ F₃) (e₁ : F₁.V ≅ G₁)
    (e₂ : F₂.V ≅ G₂) (e₃ : F₃.V ≅ G₃) : IsExt G₁ G₂ G₃ := by
  obtain ⟨S, hS, ⟨f₁⟩, ⟨f₂⟩, ⟨f₃⟩⟩ := h
  exact ⟨S.map (Action.forget _ Λ), hS.map_of_exact _, ⟨(Action.forget _ Λ).mapIso f₁ ≪≫ e₁⟩,
    ⟨(Action.forget _ Λ).mapIso f₂ ≪≫ e₂⟩, ⟨(Action.forget _ Λ).mapIso f₃ ≪≫ e₃⟩⟩

end Iso

section Chain

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O} {Λ : Type} [CommRing Λ]

def pPres (P : EPres B Λ) : Pres B where
  r := P.r
  E := P.E'.V
  E' := P.E'.V
  vb := P.vb'
  vb' := P.vb'
  ψ := smulHom _ (p : Γ(B.X, ⊤))
  iso := by
    have := Vert.Model.isIso_genRes_map_smulHom (Z := B) P.E'.V (g := (p : O))
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    have e : B.const (p : O) = (p : Γ(B.X, ⊤)) := map_natCast _ _
    rwa [e] at this

theorem exists_chain (Q : EqChain p B Λ 1) (hn : GlobalTheory.IsNormalScheme B.X) :
    ∃ Ch : Chain p B (id : Unit → Unit) 1, (∀ τ, Ch.lw τ = Q.lw.toPres) ∧ ∀ τ, Ch.oo τ = Q.oo.toPres := by
  have h01 : 0 < 1 := Nat.one_pos

  have hgγ : ∃ w : Γ(B.X, ⊤), Q.g ^ p = w * Q.γ 0 ^ p := by
    obtain ⟨u, hu⟩ := Q.g_root
    obtain ⟨v, hv⟩ := Q.γ_root 0 h01
    rw [zero_add, pow_one] at hv
    exact ⟨↑u * ↑v⁻¹, by rw [hu, hv, mul_assoc, Units.inv_mul_cancel_left]⟩
  obtain ⟨w, hw⟩ := hgγ
  have hkill : Kills Q.g (Q.l 0).mod.V :=
    kills_of_pow (X := B.X) (Fact.out : p.Prime).ne_zero hw (LocFreeQuot.smulHom_eq_zero (Q.l_free 0 h01))
  refine ⟨{
      π := Q.π
      g := Q.g
      π_root := Q.π_root
      g_root := Q.g_root
      lw := fun _ => Q.lw.toPres
      wl := fun _ => Q.wl.hom
      lw_wl := fun _ => congrArg Action.Hom.hom Q.lw_wl
      oo := fun _ => Q.oo.toPres
      q := fun n _ => (Q.q n).toPres
      l := fun n i _ => match i with
        | 0 => (Q.l n).toPres
        | _ + 1 => pPres Q.lw
      c3 := fun _ => isExt_of_isExtA Q.c3 (Examples₂.cokV _) (Examples₂.cokV _) (Examples₂.cokV _)
      step := fun n hn' _ => isExt_of_isExtA (Q.step n hn') (Examples₂.cokV _) (Examples₂.cokV _) (Examples₂.cokV _)
      l_frob := ?_
      l_last := fun n _ _ => ⟨Iso.refl _⟩
      q_frob := ?_ }, fun _ => rfl, fun _ => rfl⟩
  · intro n hn' i hi τ
    obtain rfl : n = 0 := by omega
    obtain rfl : i = 0 := by omega
    refine ⟨kills_of_iso hkill (Examples₂.cokV _), ?_⟩
    obtain ⟨e⟩ := Q.l_last 0 h01
    exact isFrob_of_iso (isFrob_frobA p Q.hp (Q.l 0).mod) (Examples₂.cokV _) ((Action.forget _ Λ).mapIso e ≪≫ Examples₂.cokV _)
  · intro n hn' τ
    refine ⟨kills_of_iso (Q.q_kill n hn') (Examples₂.cokV _), ?_⟩
    obtain ⟨e⟩ := Q.q_frob n hn'
    exact isFrob_of_iso (isFrob_frobA p Q.hp (Q.q (n + 1)).mod) (Examples₂.cokV _)
      ((Action.forget _ Λ).mapIso e.symm ≪≫ Examples₂.cokV _)

end Chain

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.CechPic GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.BundleChernComparison in

theorem chainPtsWSt_of_eqChainSt : GlobalTheory.ChainPts.EqChainSt → GlobalTheory.ChainPts.ChainPtsWSt := by
  intro h D O hO p _ W hW jc hpin z c
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c (Fact.out : p.Prime) hW
  obtain ⟨B, f, Q, hn, hrel, h1, h2⟩ := h D O hO p W hW jc hpin z 1 c
  obtain ⟨Ch, hlw, hoo⟩ := exists_chain Q hn
  refine ⟨B, f, Ch, hn, hrel, ?_, ?_⟩
  · rw [hlw]
    exact h1.isLatPres
  · rw [hoo]
    exact h2.isLatPres

end GlobalTheory.ChainPts.Forget
