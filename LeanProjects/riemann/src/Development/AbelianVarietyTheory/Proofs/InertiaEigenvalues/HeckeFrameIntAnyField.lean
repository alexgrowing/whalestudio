import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitNatCastUp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearHeckeIsogenyInverseUpToPSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFibreMapBaseChangeAndIsogenyPairIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransportStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetDescends
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PowEqOneOfLocalLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkAnyField

open GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39 GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem pow_eq_one_of_mem {T : Over Xo.X} {C : Subgroup (T ⟶ Xo.univ.t.G)} (hpP : (p : 𝓞 E) ∈ P)
    (hC : Xo.univ.t.HeckeKer T Dw P p i C) {u : T ⟶ Xo.univ.t.G} (hu : u ∈ C) : u ^ p ^ 2 = 1 := by
  refine (GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t _ (p ^ 2)).1 fun a ha => hC.2.2.1 hu a ?_
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
  rw [sq, Nat.cast_mul]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
  rwa [map_natCast] at this

theorem exists_isPair (hP : IsHeckePrime H l P p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C)
    {f : Fib Xo x ⟶ Fib Xo x'} {ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)}
    (h : IsHkIsog p x x' C f.left ψp) : ∃ f', IsPair (p ^ 2) f f' := by
  obtain ⟨hP, hco, hp, hpP, hpM⟩ := hP
  obtain ⟨⟨hfin, het, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM hC h
  obtain ⟨-, h0, hf, hact, -, hker, -⟩ := h
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hA := isAbelianScheme_fib x
  have hB := isAbelianScheme_fib x'
  have := hA.proper
  have := hB.proper
  have := hA.comm
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv x
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv x'
  have hψ : ∀ u, σ (u ≫ f) = ψp (ρ u) := fun u => GlobalTheory.HeckePoint.fibPt_injective _ (by
    rw [s₁, ← hf, e₁]; rfl)
  have one : ∀ (G : Over (Sp Ω)) [GrpObj G], (1 : 𝟙_ (Over (Sp Ω)) ⟶ G) = η[G] := fun G _ => by
    rw [Hom.one_def]; simp
  have hom : IsMonHom f := hL.rigidity _ _ _ hA hB f (by
    rw [← one, ← one]
    exact σ.injective (by rw [hψ, map_one, map_one, map_one]))
  have lin : Lin f := fun a => GlobalTheory.HeckePoint.hom_ext_pts hA.smooth fun u => σ.injective (by
    rw [← Category.assoc, ← Category.assoc, hψ, s₂, hψ, e₂, hact])
  have hkill : ∀ u : 𝟙_ (Over (Sp Ω)) ⟶ Fib Xo x, u ≫ f = 1 → u ^ p ^ 2 = 1 := fun u hu => by
    have hx : ρ u ∈ C := by rw [← hker, MonoidHom.mem_ker, ← hψ, hu, map_one]
    exact ρ.injective (by rw [map_pow, map_one, pow_eq_one_of_mem hpP hC hx])
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 (Fib Xo x) ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit _ ≫ η[Fib Xo x]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 (Fib Xo x) ^ m) (𝟙 _) ≫ μ[Fib Xo x]))
  have := hpow (p ^ 2)
  have : IsFinite f.left := hfin
  have : Etale f.left := het
  have : Surjective f.left := hsur
  obtain ⟨π, hπ⟩ := GlobalTheory.HeckePoint.exists_fac hA.smooth f (𝟙 (Fib Xo x) ^ p ^ 2) fun u hu => by
    rw [MonObj.comp_pow, Category.comp_id, hkill u hu]
  have homπ : IsMonHom π := hL.rigidity _ _ _ hB hA π (by
    rw [← IsMonHom.one_hom f, Category.assoc, hπ, IsMonHom.one_hom])
  have : Epi f.left := Flat.epi_of_flat_of_surjective _
  have : Epi f := Over.epi_of_epi_left f
  refine ⟨π, hom, homπ, hπ, ?_, lin, fun a => ?_⟩
  · rw [← cancel_epi f, ← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have := Xo.univ.t.act.hom a
    rw [← cancel_epi f, ← Category.assoc, ← lin a, Category.assoc, hπ, ← Category.assoc, hπ, MonObj.pow_comp,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]

section Ext

variable {K L : Type} [Field K] [Field L] (φ : K →+* L)

def down {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} (hw : w = spMap φ ≫ x) : (Over.mk w : Over Xo.X) ⟶ Over.mk x :=
  Over.homMk (spMap φ) hw.symm

def up {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} (hw : w = spMap φ ≫ x) :
    (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk w ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun z => down φ hw ≫ z) fun _ _ => MonObj.comp_mul _ _ _

variable {φ} {x x' : Sp K ⟶ Xo.X} {w w' : Sp L ⟶ Xo.X}

theorem up_injective (hw : w = spMap φ ≫ x) : Function.Injective (up φ hw) := fun _ _ h =>
  TorsionRat.comp_injective φ (down φ hw) rfl h

theorem weilIs_up (hw : w = spMap φ ≫ x) {n : ℤ} {a b : Over.mk x ⟶ Xo.univ.t.G} {v : Kˣ}
    (h : WeilIs Xo.univ.t.G Xo.univ.t.PP.L n a b (unitOn v)) :
    WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (up φ hw a) (up φ hw b) (unitOn (Units.map φ.toMonoidHom v)) := by
  have h₁ := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds (UnivPol.pol Xo).isAb Xo.univ.t.PP.isLB (down φ hw) h
  have e' : Units.map (down φ hw).left.appTop.hom.toMonoidHom (unitOn v) = unitOn (Units.map φ.toMonoidHom v) :=
    Units.ext (congrArg (fun q => q.hom v.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  exact e' ▸ h₁

variable [IsAlgClosed K]

theorem exists_weilIs {n : ℕ} (hn : 0 < n) {a b : Over.mk x ⟶ Xo.univ.t.G} (ha : a ^ n = 1) (hb : b ^ n = 1) :
    ∃ v : Kˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L n a b (unitOn v) := by
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x (Spec.preimage (x ≫ Xo.s)).hom (Spec.map_preimage _).symm
  obtain ⟨a, rfl⟩ := (I.onto _ hn a).1 ha
  obtain ⟨b, rfl⟩ := (I.onto _ hn b).1 hb
  exact ⟨_, I.isom _ hn a b⟩

variable [IsAlgClosed L]

theorem exists_up (hw : w = spMap φ ≫ x) {n : ℕ} (hn : 0 < n) (u : Over.mk w ⟶ Xo.univ.t.G) (hu : u ^ n = 1) :
    ∃ a, a ^ n = 1 ∧ up φ hw a = u :=
  TorsionRat.exists_eq_comp_of_isAlgClosed Xo hn φ (down φ hw) rfl u hu

theorem heckeKer_down (hw : w = spMap φ ≫ x) (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
    {C : Subgroup (Over.mk w ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk w) Dw P p i C) :
    Xo.univ.t.HeckeKer (Over.mk x) Dw P p i (C.comap (up φ hw)) := by
  refine GlobalTheory.HkSetDesc.heckeKer_comap Dw P p i Xo.univ.t (down φ hw) (up φ hw) (fun _ => rfl) hpP (up_injective hw)
    (fun u hu => (exists_up hw (pow_pos hp 2) u hu).imp fun _ h => h.2) (fun a b ha hb h => ?_) C hC
  obtain ⟨v, hv⟩ := exists_weilIs (pow_pos hp 2) ha hb
  rw [Nat.cast_pow] at hv
  have e := GlobalTheory.weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB L w _ _ _ _ 1 (weilIs_up hw hv)
    (by rw [unitOn, map_one]; exact h)
  obtain rfl : v = 1 := Units.ext (φ.injective ((congrArg Units.val e).trans (map_one φ).symm))
  rwa [unitOn, map_one] at hv

theorem isHkIsog_up (hP : IsHeckePrime H l P p) (hw : w = spMap φ ≫ x)
    {C : Subgroup (Over.mk w ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk w) Dw P p i C)
    {f : Fib Xo x ⟶ Fib Xo x'} {ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)}
    (h : IsHkIsog p x x' (C.comap (up φ hw)) f.left ψp) {g : Fib Xo w ⟶ Fib Xo w'} {g' : Fib Xo w' ⟶ Fib Xo w}
    (hg : IsBC φ f g) (hgg : IsPair (p ^ 2) g g') : ∃ χp, IsHkIsog p w w' C g.left χp := by
  obtain ⟨hP, hco, hp, hpP, hpM⟩ := hP
  have hw' := hg.2.1
  obtain ⟨⟨hfin, -, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM
    (heckeKer_down hw hp.pos hpP hC) h
  obtain ⟨hs, h0, hf, -, -, hker, hweil, hlev⟩ := h
  obtain ⟨π, p₁, p₂, hπ⟩ := PairBC.exists_proj Xo.univ.t.G x w hw
  obtain ⟨π', p₁', p₂', hπ'⟩ := PairBC.exists_proj Xo.univ.t.G x' w' hw'
  have sq := hg.2.2 π π' p₁ p₂ p₁' p₂'
  have cart : IsPullback π g.left f.left π' := by
    refine IsPullback.of_bot ?_ sq.symm hπ'.1
    rw [Over.w g, Over.w f]
    exact hπ.1
  have : IsFinite g.left := MorphismProperty.of_isPullback (P := @IsFinite) cart hfin
  have : Surjective g.left := MorphismProperty.of_isPullback (P := @Surjective) cart hsur
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv w
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv w'
  have := hgg.1
  have := hgg.2.1
  let m : (𝟙_ (Over (Sp L)) ⟶ Fib Xo w) →* (𝟙_ (Over (Sp L)) ⟶ Fib Xo w') :=
    MonoidHom.mk' (fun z => z ≫ g) fun a b => MonObj.mul_comp a b g
  let χ := σ.toMonoidHom.comp (m.comp ρ.symm.toMonoidHom)
  have hχ : ∀ u, χ (ρ u) = σ (u ≫ g) := fun u => congrArg (fun z => σ (z ≫ g)) (ρ.symm_apply_apply u)
  have hfib : ∀ u, fibPt _ u ≫ g.left = fibPt _ (χ u) := fun u => by
    obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [hχ, e₁, s₁]; rfl
  have hup : ∀ a, fibPt _ (up φ hw a) ≫ π = spMap φ ≫ fibPt _ a := fun a => by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, p₁, fibPt, fibPt, pullback.lift_fst, pullback.lift_fst]; rfl
    · rw [Category.assoc, Category.assoc, p₂, fibPt, fibPt, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.id_comp, Category.comp_id]
  have key : ∀ a, χ (up φ hw a) = up φ hw' (ψp a) := fun a => by
    refine Over.OverMorphism.ext ?_
    have e := congrArg (fun q => fibPt _ (up φ hw a) ≫ q ≫ pullback.fst _ _) sq
    simp only [Category.assoc] at e
    rw [p₁', reassoc_of% (hfib (up φ hw a)), reassoc_of% (hup a), reassoc_of% (hf a), fibPt, fibPt,
      pullback.lift_fst, pullback.lift_fst] at e
    exact e
  have unit : ∀ {y : Sp K ⟶ Xo.X} {y' : Sp L ⟶ Xo.X} (hy : y' = spMap φ ≫ y) (a : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
      toUnit _ ≫ a = up φ hy (toUnit _ ≫ a) := fun hy a => by
    show _ = down φ hy ≫ toUnit _ ≫ a
    rw [comp_toUnit_assoc]
  refine ⟨χ, by rw [hw, hw', Category.assoc, Category.assoc, hs], Over.w g, hfib, fun a u => ?_, fun v => ?_,
    Subgroup.ext fun u => ?_, fun n a b v hn hv => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [← e₂, hχ, hχ, ← s₂, Category.assoc, Category.assoc, hgg.2.2.2.2.1 a]
  · obtain ⟨v, rfl⟩ := σ.surjective v
    obtain ⟨b, hb⟩ := exists_lift_pt g.left v.left
    let u : 𝟙_ (Over (Sp L)) ⟶ Fib Xo w := Over.homMk b (by rw [← Over.w g, reassoc_of% hb, Over.w v])
    exact ⟨ρ u, (hχ u).trans (congrArg σ (Over.OverMorphism.ext hb))⟩
  · have mem : ∀ a, up φ hw a ∈ χ.ker ↔ up φ hw a ∈ C := fun a => by
      rw [MonoidHom.mem_ker, key, map_eq_one_iff _ (up_injective hw'), ← MonoidHom.mem_ker, hker, Subgroup.mem_comap]
    have tor : u ^ p ^ 2 = 1 → (u ∈ χ.ker ↔ u ∈ C) := fun hu => by
      obtain ⟨a, -, rfl⟩ := exists_up hw (pow_pos hp.pos 2) u hu
      exact mem a
    refine ⟨fun hu => (tor ?_).1 hu, fun hu => (tor (pow_eq_one_of_mem hpP hC hu)).2 hu⟩
    obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [MonoidHom.mem_ker, hχ, map_eq_one_iff _ σ.injective] at hu
    have e := congrArg (u ≫ ·) hgg.2.2.1
    simp only [← Category.assoc, hu, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at e
    rw [← map_pow, ← e, map_one]
  · have hn0 : 0 < n := Nat.pos_of_ne_zero fun e => hp.one_lt.ne' (by simpa [e] using hn)
    obtain ⟨ta, tb⟩ := GlobalTheory.PairingLawsCompare.mem_tors_of_weilIs (UnivPol.pol Xo) n hv
    obtain ⟨a, ha, rfl⟩ := exists_up hw hn0 a ta
    obtain ⟨b, hb, rfl⟩ := exists_up hw hn0 b tb
    obtain ⟨v₀, hv₀⟩ := exists_weilIs hn0 ha hb
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB L w _ _ _ _ _ (weilIs_up hw hv₀) hv
    rw [key, key, ← map_pow]
    exact weilIs_up hw' (hweil n a b v₀ hn hv₀)
  · rw [unit hw, unit hw, key, key, (hlev p' hp' a).1, (hlev p' hp' a).2, ← unit, ← unit]
    exact ⟨rfl, rfl⟩

end Ext

theorem exists_hkRelFr_down (hP : IsHeckePrime H l P p) {K L : Type} [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {y : FrPt Xo c K} {w z : FrPt Xo c L}
    (hw : FrMap φ y w) (C : hkKer (Xo := Xo) P p i L w) (hz : hkRelFr P p i (hkTr Xo c p) L w C z) :
    ∃ (C₀ : hkKer (Xo := Xo) P p i K y) (z₀ : FrPt Xo c K), hkRelFr P p i (hkTr Xo c p) K y C₀ z₀ ∧ FrMap φ z₀ z := by
  have hp := hP.2.2.1.pos
  obtain ⟨hT, hU⟩ := GlobalTheory.T.heckeIsogeny_thetaGenerator_transport E H Dw l Xo c P p i hP
  let C₀ : hkKer (Xo := Xo) P p i K y := ⟨_, heckeKer_down hw.1 hp hP.2.2.2.1 C.2⟩
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.HeckePointLaw.exists_hkRelFr hP hT K y C₀
  obtain ⟨z₁, hz₁⟩ := exists_frMap φ z₀
  refine ⟨C₀, z₀, hz₀, ?_⟩
  obtain ⟨ψ, ψp, h, hLie, hTr⟩ := hz₀
  let f : Fib Xo y.x ⟶ Fib Xo z₀.x := Over.homMk ψ h.2.1
  obtain ⟨f', hf⟩ := exists_isPair (f := f) hP C₀.2 h
  obtain ⟨g, hg⟩ := (PairBC.exists_isBC_and_isPair_iff E H Dw l Xo K L φ.toRingHom y.x z₀.x w.x z₁.x).1 hw.1 hz₁.1 f
  obtain ⟨g', hg'⟩ := (PairBC.exists_isBC_and_isPair_iff E H Dw l Xo K L φ.toRingHom z₀.x y.x z₁.x w.x).1 hz₁.1 hw.1 f'
  have e : spMap (algebraMap K K) = 𝟙 (Sp K) := Spec.map_id _
  have hR : AllRat Xo y.x (p ^ 2) := TorsionRat.allRat_of_isAlgClosure Xo (pow_pos hp 2) (F := K) y.x y.x
    (by rw [e, Category.id_comp]) fun a _ => ⟨a, by rw [e, Category.id_comp]⟩
  obtain ⟨a₁, a₂, a₃⟩ := (hkWith_iff φ hp hw hz₁ hg hg' hR).1 ⟨hf, hLie, hTr⟩
  obtain ⟨χ, hχ⟩ := isHkIsog_up (f := f) hP hw.1 C.2 h hg a₁
  rwa [GlobalTheory.HeckePointLaw.hkRelFr_unique hP hU L w C z z₁ hz ⟨g.left, χ, hχ, a₂, a₃⟩]

theorem isIntegralUpToUnits_up {cls : PtClass Xo c} {T : CDVR} {io : c.F →+* T.Fr} {K L : Type} [Field K] [Field L]
    [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {k : T.Fr →+* K} {z₀ : FrPt Xo c K} {z : FrPt Xo c L}
    (hz : FrMap φ z₀ z) (h : IsIntegralUpToUnits cls T io k z₀) :
    IsIntegralUpToUnits cls T io (φ.toRingHom.comp k) z := by
  obtain ⟨T', i, hi, j, rfl, y', h₁, h₂, w, u, hw, hb⟩ := h
  letI := (i.comp io).toAlgebra
  obtain ⟨w', hw'⟩ := exists_frMap φ w
  exact ⟨T', i, hi, φ.comp j, rfl, y', h₁, h₂, w', u, frMap_comp hw hw' fun _ => rfl, frBor_map φ hb hw' hz⟩

end GlobalTheory.HkAnyField
