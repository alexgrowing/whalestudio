import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullExtend

open ThetaPtMove

theorem isCoordPt_move {S S' : Scheme.{0}} {f : S' ⟶ S} {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) {B : Over S} (σ : T.left ⟶ B.left) [IsIso σ]
    (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    (hg : ∀ th₀, IsGenSec P₀.A P₀.L 1 th₀ → IsGenSec P₀.A P₀.L 1 (VVRank.pullS P₀.A 1 β th₀))
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {z : T ⟶ P.A} {z₀ : T₀ ⟶ P₀.A} (hz : τ ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(T₀.left, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => τ.appTop.hom (v₀ i)) := by
  obtain ⟨w, hw⟩ := hw
  have hL₀ := P₀.isLB
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ho, hu, th₀, s₀, α₀, ρ₀, U₀, t₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := H
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose t ht using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (t₀ i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ k) α₀ h₂
  obtain ⟨ρ, hρ, vρ⟩ := ConstFam.exists_gen_through (φ' := fun _ : Fin 1 => z.left) (h := τ) hw hL₀ hL₁
    (fun _ => hz.symm) ρ₀ h₃
  choose U hU hU' using fun i => symLift_move hp τ hτ hw hL₀ hL₁ (hx i) (hk i) (h₅ i)
  exact ⟨ho, (map_natCast τ.appTop.hom k) ▸ hu.map τ.appTop.hom, th, s, α, ρ, U, t,
    isGenSec_move hp τ hτ hw hL₀ hL₁ σ β hβ hth (hg _ h₁), hα, hρ,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ k) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (ht i) (h₆ i), fun i => isValueAt_move hp τ hτ hL₀ hL₁ hz vρ (ht i) (h₇ i)⟩

theorem isGenSec_base (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Sp K)) {R : Type} [CommRing R]
    (t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp K))))
    (h : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (homAt t ≫ overResι ⊤) th) := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let i : baseOver (Sp K) ⟶ overRes (T := baseOver (Sp K)) ⊤ := Over.homMk (Sp K).topIso.inv
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Scheme.toIso_inv_ι _))
  have hi : overResι (T := baseOver (Sp K)) ⊤ ≫ i = 𝟙 _ := Over.OverMorphism.ext (Sp K).topIso.hom_inv_id
  have h₁ : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (overResι ⊤) th) := fun s => by
    obtain ⟨r, hr⟩ := h (VVRank.pullS P.A 1 i s)
    have e : VVRank.pullM P.A P.L 1 i (SecM.ofSec P.A s) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have := congrArg (VVRank.pullM P.A P.L 1 (overResι ⊤)) e
    rw [VVRank.pullM_comp P.A P.isLB, hi, VVRank.pullM_id P.A P.isLB, LinearMap.map_smulₛₗ] at this
    exact ⟨_, fun j => congrArg (fun q => q.1 j) this⟩
  intro s
  obtain ⟨r, hr⟩ := isGenSec_pullS hS p₀ P t _ h₁ s
  have e := VVRank.pullM_comp P.A P.isLB 1 (homAt t) (overResι ⊤) (SecM.ofSec P.A th)
  exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e))⟩

theorem isCoordPt_fibre (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {f : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (h : IsPolFibre f P₀ P φ) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    {z : baseOver (Sp R) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(Sp K, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => (spMap f).appTop.hom (v₀ i)) := by
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap f ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap f := by
    show (spMap f ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (baseOver (Sp R)).left ⟶ (baseAt t).left := 𝟙 (Sp R)
  have : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp R)))
  exact isCoordPt_move (T := baseOver (Sp R)) (T₀ := baseOver (Sp K)) (spMap f) h.2.1 h.2.2.symm σ
    (homAt t ≫ overResι ⊤) ((Category.id_comp _).trans ht) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (isGenSec_base hS P₀ t) hx hk hz H

theorem prim_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso (L.pull φ) L') {a : G ⟶ G} {a' : G' ⟶ G'}
    (ha : a'.left ≫ φ = φ ≫ a.left) (H : LBIso L (cubeLB G ![𝟙 G, a] L)) : LBIso L' (cubeLB G' ![𝟙 G', a'] L') := by
  have i₁ := pull_isLB hL φ
  have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', a'] (L.pull φ)) := by
    let U := pushPt h.1.w (𝟙 G')
    refine LBIso.chartPull (Geo.Tor.chartPullPull L _ U.left (Category.id_comp _))
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    fin_cases i
    · exact (Category.comp_id _).symm
    · exact Over.OverMorphism.ext (ha.trans (congrArg (· ≫ a.left) (Category.id_comp _).symm))
  obtain ⟨w, hw'⟩ := id hw
  exact LBIso.trans hL' (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ hL' _ _)
    (LBIso.trans hL' i₁ (DVR.linComb_isLB _ i₁ _ _) hw.symm h₁) ⟨_, DVR.linCombIso_isGen w hw' _ _⟩

theorem exists_pointMap (hL : Laws) {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K']
    {f : K →+* K'} {P : PolAV (Sp K)} {P' : PolAV (Sp K')} {φ : P'.A.left ⟶ P.A.left} (h : IsPolFibre f P P' φ) :
    ∃ r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A), (∀ x, (r x).left ≫ φ = spMap f ≫ x.left) ∧
      Function.Injective r ∧ (∀ n : ℕ, 0 < n → ∀ y, y ^ n = 1 → ∃ x, x ^ n = 1 ∧ r x = y) ∧
      ∀ (n : ℤ) x y (c : Kˣ), WeilIs P.A P.L n x y (unitOn c) →
        WeilIs P'.A P'.L n (r x) (r y) (unitOn (Units.map f.toMonoidHom c)) := by
  have := P'.isAb.comm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h.2.1 (baseOver (Sp K')) _ rfl
  let U : Over.mk ((baseOver (Sp K')).hom ≫ spMap f) ⟶ baseOver (Sp K) :=
    Over.homMk (spMap f) ((Category.comp_id _).trans (Category.id_comp _).symm)
  let r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A) := e.symm.toMonoidHom.comp (preHom U)
  have hr : ∀ x, (r x).left ≫ φ = spMap f ≫ x.left := fun x =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (U ≫ x)))
  have inj : Function.Injective r := by
    letI := f.toAlgebra
    haveI : Flat (spMap f) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K K')
    haveI : Surjective (spMap f) := ⟨fun p => ⟨(⊥ : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap f) := Flat.epi_of_flat_of_surjective (spMap f)
    exact fun x y E => Over.OverMorphism.ext ((cancel_epi (spMap f)).1
      ((hr x).symm.trans ((congrArg (fun q => q.left ≫ φ) E).trans (hr y))))
  refine ⟨r, hr, inj, fun n hn y hy => ?_, fun n x y c H => ?_⟩
  · have hk : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : K') ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hk
    have c₁ := (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hk
    have c₂ := (hL.mulN _ P' n hn).2.2.2.2 K' (𝟙 _) hk'
    let F : {x : baseOver (Sp K) ⟶ P.A // x ^ n = 1} → {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hF : Function.Injective F := fun a b E => Subtype.ext (inj (congrArg Subtype.val E))
    haveI : Finite {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (c₂.trans_ne (by positivity))
    obtain ⟨x, hx⟩ := (hF.bijective_of_nat_card_le (c₂.trans (by rw [h.1]; exact c₁.symm)).le).2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
  · have hu : Units.map U.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map f.toMonoidHom c) :=
      Units.ext (congrArg (fun q => q.hom (c : K)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm
    refine (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ P.isLB P'.isLB h.2.1 h.2.2.symm _ _ _ _ (U ≫ x) (U ≫ y) _
      (hr x).symm (hr y).symm).2 ?_
    exact hu ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB U H

theorem fnOf_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (c : K) :
    fnOf (f c) = (spMap f).appTop.hom (fnOf c) :=
  congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

theorem exists_fullExt (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K) :
    letI := H.starRing
    ∃ o' : Full D K', (o'.ρ = f o.ρ ∧ (∀ n, 0 < n → (o'.I.ζ n : K') = f (o.I.ζ n)) ∧
      ∃ φ : o'.P.A.left ⟶ o.P.A.left, IsGrpPullback o'.P.A o.P.A (spMap f) φ ∧ LBIso o'.P.L (o.P.L.pull φ) ∧
        (∀ x, (o'.oa.act x).left ≫ φ = φ ≫ (o.oa.act x).left) ∧
        ∀ n v, 0 < n → (o'.I.ev n v).left ≫ φ = spMap f ≫ (o.I.ev n v).left) ∧
      (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧
      ∀ m j z v, o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  letI := H.starRing
  obtain ⟨P', φ, hφ, hg, hm, hw⟩ := hL.polBaseChange _ _ (spMap f) o.P
  have hp : IsGrpPullback P'.A o.P.A (spMap f) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    exact congrArg (fun q => q.left) (hm T x y).symm⟩
  have h : IsPolFibre f o.P P' φ := ⟨hg, hp, hw⟩
  obtain ⟨oa, hoa⟩ := polOActPull _ _ _ o.P P' φ hp hw (𝓞 E) o.oa
  obtain ⟨r, hr, inj, onto, weil⟩ := exists_pointMap hL h
  have uinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have hact : ∀ c x, r (x ≫ o.oa.act c) = r x ≫ oa.act c := fun c x => Over.OverMorphism.ext (hφ.hom_ext (by
    rw [hr, Over.comp_left, Over.comp_left, Category.assoc, hoa, ← Category.assoc, ← Category.assoc, hr])
    (by rw [Over.w, Over.w]))
  have tors : ∀ m a, r (o.I.ev (m ^ 2) a) ^ (m ^ 2) = 1 := fun m a => by
    rcases Nat.eq_zero_or_pos (m ^ 2) with e | e
    · rw [e, pow_zero]
    · rw [← map_pow, (o.I.onto _ e _).2 ⟨a, rfl⟩, map_one]
  have det : DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp K')) (f o.ρ) := fun τ => by
    have q := (detCond_iff_of_field_extension E H D _ _ K K' f (𝟙 _) _ _ o.P.isAb.smooth).2 o.det τ
    have e := fun n => LiePull.lieMult_pull (𝓞 E) _ _ _ _ _ φ (ofRingAct o.oa.toRingAct) (ofRingAct oa.toRingAct) hp hoa
      K' (𝟙 _) τ n
    rw [e, e, Category.id_comp]
    rwa [Category.comp_id] at q
  refine ⟨{ P := P', oa := oa, prim := prim_pull hp o.P.isLB P'.isLB hw (hoa _) o.prim, ρ := f o.ρ
            ρ_sq := by rw [← map_pow, o.ρ_sq, map_neg, map_natCast]
            det := det
            closed := ‹_›
            I := { ζ := fun n => Units.map f.toMonoidHom (o.I.ζ n)
                   ζ_prim := fun n hn => (o.I.ζ_prim n hn).map_of_injective uinj
                   ζ_pow := fun n m hn hm => by rw [← map_pow, o.I.ζ_pow n m hn hm]
                   ev := fun n v => r (o.I.ev n v)
                   add := fun n a b => by rw [o.I.add, map_mul]
                   lin := fun n c a => by rw [o.I.lin, hact]
                   ker := fun n hn a => by rw [← o.I.ker n hn a, map_eq_one_iff r inj]
                   onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
                   tower := fun n m hn hm a => by rw [← map_pow, o.I.tower n m hn hm]
                   isom := fun n hn a b => by rw [← map_zpow]; exact weil _ _ _ _ (o.I.isom n hn a b) } },
    ⟨rfl, fun _ _ => rfl, φ, hp, h.2.2.symm, hoa, fun n v _ => hr _⟩, fun m v Q => ?_, fun m j z v Q => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := onto n hn z hz
    obtain ⟨a, rfl⟩ := (o.I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one]
  · have q := ConstThetaLevel.isThetaPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) Q
    simp only [← fnOf_map] at q
    exact q
  · have q := isCoordPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) (hr (o.I.ev j z)).symm Q
    simp only [← fnOf_map] at q
    exact q

end GlobalTheory.FullExtend

end
