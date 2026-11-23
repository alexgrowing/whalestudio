import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUdeep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UDeepP

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem isUnit_n (X₁ : USetup C) : IsUnit ((X₁.ρ.n : ℕ) : C.o) := by
  haveI := C.ded
  set n := X₁.ρ.n with hn
  have hdvd : n ∣ X₁.S.r * X₁.S.N := by
    rw [X₁.ρ.N_eq]
    exact Dvd.dvd.mul_left (dvd_pow (dvd_pow_self n (by have := X₁.ρ.two_le; omega)) two_ne_zero) _
  have hu₁ : IsUnit ((n : ℕ) : X₁.o₁) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hdvd) X₁.S.unit
  have hM : IsUnit ((n : ℕ) : Γ(X₁.M.Z, ⊤)) := by
    have := hu₁.map ((X₁.M.s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of X₁.o₁)).inv.hom)
    simpa only [map_natCast] using this
  let g : X₁.M.Z ⟶ Sp C.o := X₁.π ≫ C.z
  have hD : ∀ y, (n : C.o) ∉ (g y).asIdeal := by
    intro y
    have h1 : g ⁻¹ᵁ (Sp C.o).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C.o)).inv.hom (n : C.o)) = ⊤ := by
      rw [Scheme.preimage_basicOpen]
      apply Scheme.basicOpen_of_isUnit
      have := hM.map (X₁.M.Z.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
      simpa only [map_natCast] using this
    have h2 : y ∈ g ⁻¹ᵁ (Sp C.o).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C.o)).inv.hom (n : C.o)) := by
      rw [h1]; trivial
    have h3 : g y ∈ (Sp C.o).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C.o)).inv.hom (n : C.o)) := h2
    rw [basicOpen_eq_of_affine] at h3
    exact (PrimeSpectrum.mem_basicOpen _ _).1 h3
  haveI : IsProper C.z := GlobalTheory.ProperFamily.isProper_of_isProjOver C.proj
  haveI := X₁.fin
  have hcl : IsClosed (Set.range g) := by
    have := g.isClosedMap
    simpa [Set.image_univ] using this _ isClosed_univ
  let w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : ∀ a ∈ (g (X₁.M.pt w)).asIdeal, a = 0 := by
    intro a ha
    have e : X₁.M.pt ≫ g = (spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) ≫ spMap C.b := by
      simp only [g, ← Category.assoc, X₁.comp]
      simp only [Category.assoc, UCompact.i, pullback.condition]
    have e2 : g (X₁.M.pt w) = (spMap C.b) ((spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) w) := by
      rw [show g (X₁.M.pt w) = (X₁.M.pt ≫ g) w from rfl, e]; rfl
    rw [e2] at ha
    change C.b a ∈ (((spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) w).asIdeal) at ha
    have hbot : ((spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) w).asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime _ _ _ ((spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) w).isPrime
    rw [hbot, Ideal.mem_bot] at ha
    exact C.inj (by rw [ha, map_zero])
  have hall : ∀ P : Sp C.o, P ∈ Set.range g := by
    intro P
    have hsp : g (X₁.M.pt w) ⤳ P := (PrimeSpectrum.le_iff_specializes (g (X₁.M.pt w)) P).1 (fun a ha => by
      rw [hgen a ha]; exact zero_mem _)
    exact hsp.mem_closed hcl ⟨_, rfl⟩
  by_contra hnu
  obtain ⟨m, hm, hnm⟩ := exists_max_ideal_of_mem_nonunits hnu
  obtain ⟨y, hy⟩ := hall ⟨m, hm.isPrime⟩
  exact hD y (by rw [hy]; exact hnm)

theorem moduli_point_comp_compactification_structure {K : Type} [CommRing K] (y : Sp K ⟶ Xo.XF cf) :
    y ≫ C.i ≫ C.z = y ≫ pullback.snd _ _ ≫ spMap C.b := by
  simp only [UCompact.i, Category.assoc, pullback.condition]
  rw [← Category.assoc C.iF, C.iF_over]

theorem exists_fg_over {o₂ o₃ Ω : Type} [CommRing o₂] [CommRing o₃] [Field Ω] [Algebra o₂ Ω] [Algebra o₃ Ω]
    (h₂ : Algebra.FiniteType ℤ o₂) (R : Subalgebra o₂ Ω) (hR : R.FG) :
    ∃ R₃ : Subalgebra o₃ Ω, R₃.FG ∧ ∀ x ∈ R, x ∈ R₃ := by
  obtain ⟨t, ht⟩ := hR
  obtain ⟨s, hs⟩ := h₂.out
  refine ⟨Algebra.adjoin o₃ ((t : Set Ω) ∪ (s.image (algebraMap o₂ Ω) : Set Ω)),
    Subalgebra.fg_def.2 ⟨_, (t.finite_toSet.union (s.image _).finite_toSet), rfl⟩, ?_⟩
  set R₃ := Algebra.adjoin o₃ ((t : Set Ω) ∪ (s.image (algebraMap o₂ Ω) : Set Ω))
  have hb : ∀ a : o₂, algebraMap o₂ Ω a ∈ R₃ := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (s : Set o₂) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inr (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap m => simpa using intCast_mem R₃ m
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  intro x hx
  rw [← ht] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (Or.inl hx)
  | algebraMap a => exact hb a
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem exists_rebase {o₂ o₃ Ω : Type} [CommRing o₂] [CommRing o₃] [Field Ω] [Algebra o₂ Ω] [Algebra o₃ Ω]
    [b₂ : ArithBase o₂ Ω] [b₃ : ArithBase o₃ Ω] (R : Subalgebra o₂ Ω) (hR : R.FG) (P : PolAV (Sp R)) (K : ℕ)
    (ze : o₂ˣ) (ze₃ : o₃ˣ) (hz : algebraMap o₃ Ω ze₃ = algebraMap o₂ Ω ze)
    (lev : Out.Level P K (unitOn (Units.map (algebraMap o₂ R : o₂ →* R) ze))) :
    ∃ (R₃ : Subalgebra o₃ Ω) (ι : R →+* R₃) (P₃ : PolAV (Sp R₃)) (φ : P₃.A.left ⟶ P.A.left), R₃.FG ∧
      (∀ x ∈ R, x ∈ R₃) ∧ (∀ a, ((ι a : R₃) : Ω) = a) ∧ P₃.g = P.g ∧ IsGrpPullback P₃.A P.A (spMap ι) φ ∧
      LBIso P₃.L (P.L.pull φ) ∧
      Nonempty (Out.Level P₃ K (unitOn (Units.map (algebraMap o₃ R₃).toMonoidHom ze₃))) := by
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨R₃, hR₃, hle⟩ := exists_fg_over (o₃ := o₃) b₂.ft R hR
  let ι : R →+* R₃ := R.val.toRingHom.codRestrict R₃ fun x => hle _ x.2
  have hι : Function.Injective ι := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI := b₂.ded
  haveI := b₃.ded
  haveI := (Subalgebra.fg_iff_finiteType R).1 hR
  haveI := (Subalgebra.fg_iff_finiteType R₃).1 hR₃
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing o₂ R
  haveI : IsNoetherianRing R₃ := Algebra.FiniteType.isNoetherianRing o₃ R₃
  obtain ⟨P₃, φ, hg, hpb, hlb⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 ι P
  have e : Units.map ι.toMonoidHom (Units.map (algebraMap o₂ R : o₂ →* R) ze) =
      Units.map (algebraMap o₃ R₃).toMonoidHom ze₃ := Units.ext (Subtype.ext hz.symm)
  have hprim := (SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).1 lev.prim
  obtain ⟨lev₃, -⟩ := exists_level_baseChange hL _ _ _ P P₃ φ hpb (LBIso.symm hlb) hg _ _
    (unitOn (Units.map (algebraMap o₃ R₃).toMonoidHom ze₃)) (by rw [GSetup.map_unitOn', e])
    ((SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).2
      (e ▸ hprim.map_of_injective (f := Units.map ι.toMonoidHom) (Units.map_injective hι))) lev
  exact ⟨R₃, ι, P₃, φ, hR₃, hle, fun _ => rfl, hg, hpb, LBIso.symm hlb, ⟨lev₃⟩⟩

theorem exists_base (X₁ : USetup C) (Ω₂ : Type) [Field Ω₂] [Algebra X₁.Ω₁ Ω₂] (ζ : Ω₂ˣ) (K : ℕ) (hK : 1 ≤ K)
    (hζ : ζ ^ K = 1) :
    ∃ (o₃ : Type) (_ : CommRing o₃) (_ : Algebra o₃ Ω₂) (_ : ArithBase o₃ Ω₂) (κ : C.o →+* o₃) (ze : o₃ˣ), κ.Finite ∧
      algebraMap o₃ Ω₂ ze = ζ ∧
      (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.uΩ) ≫ C.i ≫ C.z = spMap ((algebraMap o₃ Ω₂).comp κ) := by
  haveI := C.ded
  haveI : CharZero X₁.Ω₁ := ArithBase.char X₁.o₁
  haveI : CharZero Ω₂ := charZero_of_injective_algebraMap (algebraMap X₁.Ω₁ Ω₂).injective
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  obtain ⟨β, hβ⟩ := Spec.map_surjective
    ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.uΩ) ≫ pullback.snd _ _ : Sp Ω₂ ⟶ Sp cf.F)
  obtain ⟨o₃, _, _, κ, ze, hded, hκ, hinj, hc, hze⟩ := GSetup.exists_base_root C.o cf.F Ω₂ β.hom ζ K hK hζ
  have hft : Algebra.FiniteType ℤ o₃ := by
    have h₁ : (Int.castRingHom C.o).FiniteType := by
      have := C.ft
      exact RingHom.finiteType_algebraMap.2 this
    have h₂ := RingHom.FiniteType.comp hκ.finiteType h₁
    rw [RingHom.ext_int (κ.comp (Int.castRingHom C.o)) (algebraMap ℤ o₃)] at h₂
    exact RingHom.finiteType_algebraMap.1 h₂
  refine ⟨o₃, _, _, ⟨hded, hft, inferInstance, hinj⟩, κ, ze, hκ, congrArg Units.val hze, ?_⟩
  rw [moduli_point_comp_compactification_structure, ← Category.assoc, ← hβ, hc]
  exact UDeepEx.spMap_comp C.b β.hom

theorem exists_model (X₁ : USetup C) (o₃ Ω₂ : Type) [CommRing o₃] [Field Ω₂] [Algebra o₃ Ω₂] [ArithBase o₃ Ω₂]
    [Algebra X₁.Ω₁ Ω₂] [FiniteDimensional X₁.Ω₁ Ω₂] (κ : C.o →+* o₃) (hκ : κ.Finite)
    (hc : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.uΩ) ≫ C.i ≫ C.z = spMap ((algebraMap o₃ Ω₂).comp κ)) :
    ∃ (M : RatModel o₃ Ω₂) (q : M.Z ⟶ X₁.M.Z), GlobalTheory.IsNormalScheme M.Z ∧ IsFinite q ∧
      M.pt ≫ q = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt := by
  haveI := C.ded
  haveI : IsProper C.z := GlobalTheory.ProperFamily.isProper_of_isProjOver C.proj
  haveI := X₁.fin
  have hp : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt) ≫ X₁.π ≫ C.z = spMap ((algebraMap o₃ Ω₂).comp κ) := by
    rw [← hc, Category.assoc, ← Category.assoc X₁.M.pt, X₁.comp]
    simp only [Category.assoc]
  have hst : ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt).stalkMap (genericPoint (Sp Ω₂))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (stalkMap_spMap_finite _ (RingHom.finite_algebraMap.2 inferInstance) _)
      (RingHom.Finite.of_surjective _ (RatModel.stalkMap_pt_surjective X₁.M _))
  obtain ⟨M, q, hn, hq, hpt⟩ := exists_ratModel_normalization C.o o₃ Ω₂ κ hκ X₁.M.Z (X₁.π ≫ C.z) inferInstance
    inferInstance inferInstance _ hp hst
  exact ⟨M, q, GlobalTheory.IsNormalScheme.of_pred hn, hq, hpt⟩

theorem exists_udeep_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (m₀ : ℕ),
      ∃ D : UDeep X₁, m₀ ≤ D.m ∧ IsProjOver D.X.M.s := by
  intro E _ _ _ H Dw _ l Xo cf C X₁ m₀
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j, hk, hB, hj, big⟩ :=
    UDeepEx.big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 ((X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) * max m₀ 1) ^ 2)
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  have hunK : IsUnit ((((X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 : ℕ)) : X₁.o₁) := by
    push_cast
    exact ((hun1.pow _).mul ((hun1.pow _).pow _)).pow _
  have hKpos : 0 < (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 := by have := hℓp.pos; positivity
  obtain ⟨o₁, Ω₂, _, _, _, _, _, -, fd, gal, -, -, R₀, h₀, P₀, ψ₀, ze₀, hfg₀, hfr₀, hh₀, hPg₀, hpb₀, hlb₀, ⟨lev₀⟩⟩ :=
    UDeepEx.exists_level X₁ _ hKpos hunK
  have hζ : Units.map (algebraMap o₁ Ω₂).toMonoidHom ze₀ ^ (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 = 1 := by
    have h₁ := ((SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).1 lev₀.prim).pow_eq_one
    have h₂ := congrArg (Units.map R₀.val.toRingHom.toMonoidHom) h₁
    rw [map_pow, map_one] at h₂
    exact h₂
  obtain ⟨o₂, _, _, _, κ, ze, hκ, hze, hc⟩ := exists_base X₁ Ω₂ _ _ hKpos hζ
  obtain ⟨R, ι, P, φ₀, hfg, hle₀, hι, hPg₁, hpb₁, hlb₁, ⟨lev⟩⟩ := exists_rebase R₀ hfg₀ P₀ _ ze₀ ze hze lev₀
  have hfr : ∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b := fun x =>
    let ⟨a, ha, b, hb, e⟩ := hfr₀ x
    ⟨a, hle₀ a ha, b, hle₀ b hb, e⟩
  let h : X₁.S.R →+* R := ι.comp h₀
  have hh : ∀ a, ((h a : R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => (hι _).trans (hh₀ a)
  have hPg : P.g = X₁.ρ.P.g := hPg₁.trans hPg₀
  let ψ := φ₀ ≫ ψ₀
  have hpb : IsGrpPullback P.A X₁.ρ.P.A (spMap h) ψ := by
    rw [← UDeepEx.spMap_comp]
    exact hpb₁.comp hpb₀
  have hlb : LBIso P.L (X₁.ρ.P.L.pull ψ) :=
    LBIso.trans P.isLB (pull_isLB P₀.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₁ (UDeepEx.lbIso_pull_comp hlb₀ φ₀ rfl)
  clear_value h ψ
  have hS := GlobalTheory.Poinc.hypS_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using (isUnit_n X₁).map κ
  obtain ⟨S₂, ρ₂, hR, φ, -, hN₂, hr₂, hg₂, hpb₂, hlb₂, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk hj hun2 hS lev
  set h' : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hh'
  have hval : ∀ a, ((h' a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hpb' : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap h') (φ ≫ ψ) := by
    rw [hh', ← UDeepEx.spMap_comp]
    exact hpb₂.comp hpb
  have hlb' : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (UDeepEx.lbIso_pull_comp hlb φ rfl)

  have hsub : ∀ x : ratHull X₁.S.R, algebraMap X₁.Ω₁ Ω₂ x ∈ ratHull S₂.R := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn, hnx⟩ := mem_ratHull.1 hx
    refine mem_ratHull.2 ⟨n, hn, ?_⟩
    have e : (n : Ω₂) * algebraMap X₁.Ω₁ Ω₂ x = ((h' ⟨_, hnx⟩ : S₂.R) : Ω₂) := by
      rw [hval]; simp
    rw [e]; exact (h' ⟨_, hnx⟩).2
  let τ : ratHull X₁.S.R →+* ratHull S₂.R :=
    ((algebraMap X₁.Ω₁ Ω₂).comp (ratHull X₁.S.R).val.toRingHom).codRestrict _ hsub
  have hτ : (toRat S₂.R).comp h' = τ.comp (toRat X₁.S.R) := by
    ext a
    exact hval a
  have key : spMap (ratHull S₂.R).val.toRingHom ≫ spMap τ =
      spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [UDeepEx.spMap_comp, UDeepEx.spMap_comp]
    rfl
  have hpulled : UOver Xo cf ρ₂.P (toRat S₂.R) (spMap τ ≫ X₁.u) := by
    rw [uOver_baseChange_iff hpb' hlb', hτ]
    exact X₁.pulled.comp τ
  have hpt : spMap (ratHull S₂.R).val.toRingHom ≫ spMap τ ≫ X₁.u = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.uΩ := by
    rw [← Category.assoc, key, Category.assoc]
  have hgen : ∀ w, (spMap (ratHull S₂.R).val.toRingHom ≫ spMap τ ≫ X₁.u) w ∈ genericPoints (Xo.XF cf) := by
    intro w
    rw [hpt, Scheme.Hom.comp_apply]
    exact X₁.gen _
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := exists_model X₁ o₂ Ω₂ κ hκ hc
  haveI := hq
  haveI := X₁.fin
  have hcomp : M₂.pt ≫ q ≫ X₁.π = spMap (ratHull S₂.R).val.toRingHom ≫ (spMap τ ≫ X₁.u) ≫ C.i := by
    rw [← Category.assoc, hqgen, Category.assoc, X₁.comp, ← Category.assoc (spMap (algebraMap X₁.Ω₁ Ω₂)), ← key]
    simp only [Category.assoc]
  have hbig : S₂.Big := big j le_rfl o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : USetup C := USetup.mk o₂ Ω₂ S₂ ρ₂ hbig (spMap τ ≫ X₁.u) hpulled hgen M₂ hMn (q ≫ X₁.π) inferInstance hcomp
  have hle : X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) * max m₀ 1 ≤ X₁.ρ.n ^ k :=
    (Nat.pow_le_pow_iff_left two_ne_zero).1 hB
  have hpos : 1 ≤ X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := Nat.one_le_pow _ _ (by omega)
  have hm₁ : 1 ≤ max m₀ 1 := le_max_right _ _
  have hm₀ : m₀ ≤ X₁.ρ.n ^ k :=
    (le_max_left m₀ 1).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans hle)
  have hdm : X₁.S.r * X₁.S.N ∣ X₁.ρ.n ^ k := by
    rw [hL₁]
    refine pow_dvd_pow _ ((Nat.pow_le_pow_iff_right hℓ2).1 ?_)
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans hle
  have hd₂ : X₁.S.r * X₁.S.N ∣ S₂.r * S₂.N := by
    rw [hN₂]
    exact (hdm.trans (dvd_pow_self _ two_ne_zero)).trans (dvd_mul_left _ _)
  obtain ⟨lab, hsame, hrange⟩ :=
    GlobalTheory.T.exists_thetaLabel_common_generic_fibre_pullback X₁.S S₂ X₁.ρ ρ₂ (fun _ => 𝟙 _) (fun _ => 𝟙 _) (algebraMap X₁.Ω₁ Ω₂) h' (φ ≫ ψ) hval hpb' hlb'
      (fun _ => by simp) hd₂
  have hsame' : USame X₁.ρ ρ₂ lab (algebraMap X₁.Ω₁ Ω₂) := by
    obtain ⟨P₀, a, a', -, h₁, h₂, h₃, h₄, -, h₅⟩ := hsame
    exact ⟨P₀, a, a', h₁, h₂, h₃, h₄, h₅⟩
  have hproj : IsProjOver X₂.M.s :=
    GlobalTheory.UPoinc.ProjOverBase.isProjOver_model E H Dw l Xo cf C X₂ κ ((congrArg (· ≫ C.i ≫ C.z) hpt).trans hc)
  exact ⟨UDeep.mk (X := X₂) fd gal hpt q hq hqgen rfl (X₁.ρ.n ^ k) hN₂ hdm lab hsame' hrange, hm₀, hproj⟩

end GlobalTheory.UPoinc.UDeepP
