import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecGroup

section General

variable {S : Scheme.{0}} {G T T' : Over S}

theorem left_mul_of_comp [GrpObj G] (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom) {a b : T ⟶ G} {a' b' : T' ⟶ G}
    (ha : a'.left = r ≫ a.left) (hb : b'.left = r ≫ b.left) : (a' * b').left = r ≫ (a * b).left := by
  have e₁ : a' = Over.homMk r hr ≫ a := Over.OverMorphism.ext ha
  have e₂ : b' = Over.homMk r hr ≫ b := Over.OverMorphism.ext hb
  rw [e₁, e₂, ← MonObj.comp_mul]
  rfl

theorem left_one [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem map_zero_eq_one {V M : Type} [AddGroup V] [Group M] (x : V → M) (h : ∀ v v', x (v + v') = x v * x v') :
    x 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem ext_of_generic {A K : Type} [CommRing A] [Field K] {j : A →+* K} (hj : Function.Injective j)
    [IsSeparated G.hom] {p : Sp A ⟶ S} {a b : Over.mk p ⟶ G} (h : spMap j ≫ a.left = spMap j ≫ b.left) : a = b := by
  have : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have : IsDomain A := hj.isDomain j
  exact Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp A) G.hom ((Over.w a).trans (Over.w b).symm) (spMap j) h)

theorem le_preimage_of_unit {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have h₀ : spMap ρ (⊥ : PrimeSpectrum K) ∈ x ⁻¹ᵁ U := h (x := (⊥ : PrimeSpectrum K)) trivial
  have hs : (show PrimeSpectrum A from p) ⤳ (show PrimeSpectrum A from spMap ρ (⊥ : PrimeSpectrum K)) := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun s hs => ?_
    change ρ s ∈ (⊥ : Ideal K)
    rw [Ideal.mem_bot]
    by_contra hne
    exact (show PrimeSpectrum A from p).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (hρ s hne))
  exact hs.mem_open (x ⁻¹ᵁ U).isOpen h₀

theorem isFrm_map {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (L : LB X) (x : Sp A ⟶ X) (τ : L.ι → A) (h : IsFrm L x τ) :
    IsFrm L (spMap ρ ≫ x) (fun j => ρ (τ j)) := by
  refine ⟨fun j hj => (h.1 j (le_preimage_of_unit ρ hρ x _ hj)).map ρ, fun j j' hj => ?_⟩
  have hx := le_preimage_of_unit ρ hρ x _ hj
  rw [HolHom.valR_spMap ρ x _ hx, ← map_mul, ← h.2 j j' hx]

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ : GenPts A t y} {Γ : Germs} (Ψ : SpecPts Φ Γ)
  {w : ℂ} (hw : Ψ.T < w.im)

theorem val_base :
    spMap (Γ.R w).val.toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = y := by
  rw [← Category.assoc, spMap_comp_spMap]
  exact Ψ.yT_gen

theorem ev_base :
    spMap (Γ.ev w).toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = Ψ.yw w := by
  rw [← Category.assoc, spMap_comp_spMap, Ψ.yw_eq w hw]
  congr 2
  exact RingHom.ext fun s => Γ.ev_eq Ψ.T w hw s

theorem xt_add (v v' : A.V) : Ψ.xt w hw (v + v') = Ψ.xt w hw v * Ψ.xt w hw v' := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.add]
  exact left_mul_of_comp (T' := Over.mk y) _ (val_base Ψ hw) (Ψ.xt_gen w hw v).symm (Ψ.xt_gen w hw v').symm

theorem xt_act (e : 𝓞 E) (v : A.V) : Ψ.xt w hw (A.actV e v) = Ψ.xt w hw v ≫ t.act.act e := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.lin, Over.comp_left, Over.comp_left, ← Ψ.xt_gen w hw v, Category.assoc]

include hw

theorem pi_add (v v' : A.V) : Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v' := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_add]
  exact (left_mul_of_comp (T' := Over.mk (Ψ.yw w)) _ (ev_base Ψ hw) (Ψ.pi_eq w hw v) (Ψ.pi_eq w hw v')).symm

theorem pi_act (e : 𝓞 E) (v : A.V) : Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ t.act.act e := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_act, Over.comp_left, Over.comp_left, Ψ.pi_eq w hw, Category.assoc]

theorem pi_frm (v : A.V) : IsFrm t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v) := by
  rw [Ψ.pi_eq w hw]
  exact isFrm_map (Γ.ev w).toRingHom (Γ.unit w) _ _ _ (Ψ.τt_frm w hw v)

theorem pi_rig (j : t.PP.L.ι) (hj : ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ t.PP.L.U j) :
    Ψ.fr w j 0 = valAt' (Ψ.yw w) ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
  rw [Ψ.pi_eq w hw] at hj
  have h₁ : ⊤ ≤ (Ψ.xt w hw 0).left ⁻¹ᵁ t.PP.L.U j := le_preimage_of_unit (Γ.ev w).toRingHom (Γ.unit w) _ _ hj
  have h₂ : ⊤ ≤ (Φ.x 0).left ⁻¹ᵁ t.PP.L.U j := by
    rw [← Ψ.xt_gen w hw 0]
    exact fun p _ => h₁ (x := spMap (Γ.R w).val.toRingHom p) trivial
  have h₃ : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ
      (t.PP.L.pull (eSec t.G)).U (fun _ => j) := by
    rw [map_zero_eq_one _ (xt_add Ψ hw), left_one] at h₁
    exact fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  have h₄ : Ψ.τt w 0 j = valR (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)
      ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
    refine Subtype.ext ?_
    rw [Ψ.τt_gen w hw 0 j h₁, Φ.rig j h₂]
    exact (congrArg (fun q => valR q _ _) (val_base Ψ hw).symm).trans
      (HolHom.valR_spMap (Γ.R w).val.toRingHom _ _ h₃ _)
  rw [SpecPts.fr, h₄, HolHom.valAt'_eq_valR, ← ev_base Ψ hw]
  exact (HolHom.valR_spMap (Γ.ev w).toRingHom _ _ h₃ _).symm

omit hw

theorem specPts_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ w : ℂ, Ψ.T < w.im → (∀ v v', Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v') ∧ (∀ (e : 𝓞 E) v, Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ o.t.act.act e) ∧ (∀ v, IsFrm o.t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v)) ∧ ∀ j, ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j 0 = valAt' (Ψ.yw w) ((o.t.PP.L.pull (eSec o.t.G)).U (fun _ => j)) (o.t.PP.rig.s (fun _ => j)).val :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ψ _ hw =>
    ⟨pi_add Ψ hw, pi_act Ψ hw, pi_frm Ψ hw, pi_rig Ψ hw⟩

end GlobalTheory.SpecGroup
