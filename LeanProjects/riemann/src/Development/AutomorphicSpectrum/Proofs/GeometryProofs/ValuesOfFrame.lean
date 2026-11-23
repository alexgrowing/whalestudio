import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FrameVal

section Linear

theorem iSupIndep_eigSp {F W O I : Type} [Field F] [AddCommGroup W] [Module F W] [CommRing O]
    (ρ : O →+* Module.End F W) (χ : I → (O →+* F)) (hχ : Function.Injective χ) :
    iSupIndep fun i => eigSp ρ (χ i) := by
  have hc : ∀ a b, Commute (ρ a) (ρ b) := fun a b => by
    show ρ a * ρ b = ρ b * ρ a
    rw [← map_mul, ← map_mul, mul_comm]
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : O => ρ a)
    (fun a b c => Module.End.mapsTo_maxGenEigenspace_of_comm (hc b a) c)
  have h2 := h.comp (f := fun i => (fun a => χ i a : O → F)) fun i j e =>
    hχ (RingHom.ext fun a => congrFun e a)
  refine h2.mono fun i x hx => ?_
  refine (Submodule.mem_iInf _).2 fun a => ?_
  have h3 := (Submodule.mem_iInf _).1 hx a
  refine Module.End.mem_maxGenEigenspace _ _ _ |>.2 ⟨1, ?_⟩
  simpa [sub_eq_zero, Module.algebraMap_end_apply] using h3

theorem exists_coords {Ω Li : Type} [Field Ω] [AddCommGroup Li] [Module Ω Li] {m : ℕ} (v : Fin m → Li)
    (hv : LinearIndependent Ω v) (U : Submodule Ω Li) (hU : Disjoint (Submodule.span Ω (Set.range v)) U) :
    ∃ π : Li →ₗ[Ω] (Fin m → Ω), (∀ k, π (v k) = Pi.single k 1) ∧ ∀ x ∈ U, π x = 0 := by
  classical
  have h2 : LinearIndependent Ω (U.mkQ ∘ v) := hv.map (by simpa using hU)
  have hinj := h2.fintypeLinearCombination_injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨g ∘ₗ U.mkQ, fun k => ?_, fun x hx => ?_⟩
  · have := LinearMap.congr_fun hg (Pi.single k 1)
    simpa [Fintype.linearCombination_apply_single] using this
  · simp [(Submodule.Quotient.mk_eq_zero U).2 hx]

theorem values_basis {A Ω L Li V T I : Type} [CommRing A] [Field Ω] [Field L] [AddCommGroup Li] [Module Ω Li]
    [AddCommGroup V] [Module L V] [AddCommGroup T] [Module A T] [Fintype I] [DecidableEq I]
    (g : A →+* Ω) (hg : Function.Injective g) (v : A →+* L) (i : T →+ Li) (hi : ∀ (a : A) t, i (a • t) = g a • i t)
    (β : T →+ V) (hβ : ∀ (a : A) t, β (a • t) = v a • β t)
    (hlift : ∀ ψ : T →+ L, (∀ (a : A) t, ψ (a • t) = v a * ψ t) → ∃ F : V →ₗ[L] L, ∀ t, F (β t) = ψ t)
    (hgen : ∀ P : Submodule L V, (∀ t, β t ∈ P) → P = ⊤)
    (Vg : I → Submodule Ω Li) (hVg : iSupIndep Vg) (W : I → Submodule L V) (hW : iSupIndep W)
    (hdec : ∀ t, ∃ f : I → T, (∀ j, i (f j) ∈ Vg j) ∧ t = ∑ j, f j)
    (hβW : ∀ j t, i t ∈ Vg j → β t ∈ W j)
    (lab : I) {m : ℕ} (b : Fin m → T) (hb : LinearIndependent Ω fun k => i (b k))
    (hbV : ∀ k, i (b k) ∈ Vg lab)
    (hsp : ∀ t, i t ∈ Vg lab → ∃ r : Fin m → A, t = ∑ k, r k • b k) :
    LinearIndependent L (fun k => β (b k)) ∧ Submodule.span L (Set.range fun k => β (b k)) = W lab := by

  have hdisj : Disjoint (Submodule.span Ω (Set.range fun k => i (b k))) (⨆ j, ⨆ (_ : j ≠ lab), Vg j) :=
    (hVg lab).mono_left (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hbV k))
  obtain ⟨π, hπ, hπ0⟩ := exists_coords _ hb _ hdisj
  have hπV : ∀ j, j ≠ lab → ∀ t, i t ∈ Vg j → π (i t) = 0 := fun j hj t ht =>
    hπ0 _ (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj ht))

  have key : ∀ t, ∃ r : Fin m → A, ∀ k, π (i t) k = g (r k) := by
    intro t
    obtain ⟨f, hf, rfl⟩ := hdec t
    obtain ⟨r, hr⟩ := hsp _ (hf lab)
    refine ⟨r, fun k => ?_⟩
    have h1 : π (i (∑ j, f j)) = π (i (f lab)) := by
      rw [map_sum, map_sum, Finset.sum_eq_single lab (fun j _ hj => hπV j hj _ (hf j)) (by simp)]
    rw [h1, hr, map_sum, map_sum]
    simp only [hi, map_smul, hπ]
    simp [Finset.sum_apply, Pi.single_apply]
  choose c hc using key
  have hcb : ∀ j k, c (b j) k = if k = j then 1 else 0 := fun j k => hg (by
    rw [← hc, hπ, Pi.single_apply]
    split_ifs <;> simp)
  have hadd : ∀ t t' k, c (t + t') k = c t k + c t' k := fun t t' k => hg (by
    rw [← hc, map_add, map_add, map_add, ← hc, ← hc]; rfl)
  have hsm : ∀ (a : A) t k, c (a • t) k = a * c t k := fun a t k => hg (by
    rw [← hc, hi, map_smul, map_mul, ← hc]; rfl)
  have hF : ∀ k, ∃ F : V →ₗ[L] L, ∀ t, F (β t) = v (c t k) := fun k =>
    hlift (AddMonoidHom.mk' (fun t => v (c t k)) fun t t' => by simp [hadd]) fun a t => by simp [hsm]
  choose F hFβ using hF
  refine ⟨Fintype.linearIndependent_iff.2 fun w hw k => ?_, le_antisymm ?_ fun x hx => ?_⟩
  · have := congrArg (F k) hw
    simp only [map_sum, map_smul, hFβ, hcb, map_zero, smul_eq_mul] at this
    simpa using this
  · exact Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hβW _ _ (hbV k))
  · set S := Submodule.span L (Set.range fun k => β (b k)) with hS
    have hSle : S ≤ W lab := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hβW _ _ (hbV k))
    have htop : S ⊔ (⨆ j, ⨆ (_ : j ≠ lab), W j) = ⊤ := hgen _ fun t => by
      obtain ⟨f, hf, rfl⟩ := hdec t
      rw [map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j = lab
      · subst hj
        refine Submodule.mem_sup_left ?_
        obtain ⟨r, hr⟩ := hsp _ (hf j)
        rw [hr, map_sum]
        refine Submodule.sum_mem _ fun k _ => ?_
        rw [hβ]
        exact S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hβW j _ (hf j))))
    have hx' : x ∈ S ⊔ (⨆ j, ⨆ (_ : j ≠ lab), W j) := by rw [htop]; trivial
    obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    have hw' : w ∈ W lab := by
      have := (W lab).sub_mem hx (hSle ha)
      simpa using this
    have h0 : w = 0 := (Submodule.disjoint_def.1 (hW lab)) w hw' hw
    simpa [h0] using ha

end Linear

section Stalk

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]

theorem exists_model_of_eq {R : Type} [CommRing R] {z z' : Sp R ⟶ X} (h : z = z') {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G z E) : ∃ M' : LieModel G z' E, ∀ e, (M'.pt e).left = (M.pt e).left := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem stalk_model [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (hξ : IsCptGen ξ) {L : Type} [Field L] (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {V : Type} [AddCommGroup V]
    [Module L V] (Mz : LieModel G z V) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module (X.presheaf.stalk (centre z)) T)
      (M0 : LieModel (R := X.presheaf.stalk (centre z)) G (X.fromSpecStalk (centre z)) T) (i : T →+ Li) (β : T →+ V),
      (∀ t, M.Extends ⟨centre z, h⟩ (i t) (M0.pt t)) ∧
      (∀ t, Mz.pt (β t) = LieTangent.epsBase _ (LieTangent.spec_centre z) ≫ M0.pt t) ∧
      (∀ (a : X.presheaf.stalk (centre z)) t, i (a • t) = genMap ξ ⟨centre z, h⟩ a • i t) ∧
      (∀ (a : X.presheaf.stalk (centre z)) t, β (a • t) = (Scheme.stalkClosedPointTo z).hom a • β t) ∧
      (∀ e ∈ M.lat ⟨centre z, h⟩, ∃ t, i t = e) ∧
      (∀ ψ : T →+ L, (∀ (a : X.presheaf.stalk (centre z)) t, ψ (a • t) = (Scheme.stalkClosedPointTo z).hom a * ψ t) →
        ∃ F : V →ₗ[L] L, ∀ t, F (β t) = ψ t) ∧
      ∀ P : Submodule L V, (∀ t, β t ∈ P) → P = ⊤ := by
  obtain ⟨T, iT, mT, ⟨M0⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  let q : Cpt ξ := ⟨centre z, h⟩
  have exi : ∀ t, ∃ e, M.pt e = LieTangent.epsBase (genMap ξ q) (LieTangent.spec_genMap ξ q) ≫ M0.pt t := fun t =>
    M.onto _ (LieTangent.isTanAt_base _ _ (M0.tan t))
  choose fi hfi using exi
  have exb : ∀ t, ∃ x, Mz.pt x = LieTangent.epsBase _ (LieTangent.spec_centre z) ≫ M0.pt t := fun t =>
    Mz.onto _ (LieTangent.isTanAt_base _ _ (M0.tan t))
  choose fb hfb using exb
  let i : T →+ Li := AddMonoidHom.mk' fi fun a b => M.inj (by rw [M.add, hfi, hfi, hfi, M0.add, comp_mul])
  let β : T →+ V := AddMonoidHom.mk' fb fun a b => Mz.inj (by rw [Mz.add, hfb, hfb, hfb, M0.add, comp_mul])
  have hi : ∀ t, M.pt (i t) = LieTangent.epsBase (genMap ξ q) (LieTangent.spec_genMap ξ q) ≫ M0.pt t := hfi
  have hβ : ∀ t, Mz.pt (β t) = LieTangent.epsBase _ (LieTangent.spec_centre z) ≫ M0.pt t := hfb
  have hext : ∀ t, M.Extends q (i t) (M0.pt t) := fun t => (M.extends_iff _ _ _).2 ⟨M0.tan t, hi t⟩
  have hsi : ∀ (a : X.presheaf.stalk (centre z)) t, i (a • t) = genMap ξ q a • i t := fun a t => M.inj (by
    rw [hi, LieModel.pt_smul, LieModel.pt_smul, hi, ← Category.assoc, LieTangent.base_scale, Category.assoc])
  have hsβ : ∀ (a : X.presheaf.stalk (centre z)) t, β (a • t) = (Scheme.stalkClosedPointTo z).hom a • β t :=
    fun a t => Mz.inj (by
      rw [hβ, LieModel.pt_smul, LieModel.pt_smul, hβ, ← Category.assoc, LieTangent.base_scale, Category.assoc]
      rfl)
  have honto : ∀ e ∈ M.lat q, ∃ t, i t = e := by
    intro e he
    obtain ⟨w, hw⟩ := (M.mem_lat_iff q e).1 he
    obtain ⟨t, rfl⟩ := M0.onto w hw.1
    refine ⟨t, M.inj ?_⟩
    rw [hi, ((M.extends_iff _ _ _).1 hw).2]
  letI alg : Algebra (X.presheaf.stalk (centre z)) L := (Scheme.stalkClosedPointTo z).hom.toAlgebra
  letI mV : Module (X.presheaf.stalk (centre z)) V := Module.compHom V (Scheme.stalkClosedPointTo z).hom
  have hmV : ∀ (a : X.presheaf.stalk (centre z)) (x : V), a • x = (Scheme.stalkClosedPointTo z).hom a • x :=
    fun _ _ => rfl
  haveI tower : IsScalarTower (X.presheaf.stalk (centre z)) L V :=
    ⟨fun a b x => by rw [Algebra.smul_def, hmV, mul_smul]; rfl⟩
  obtain ⟨M', hM'⟩ := exists_model_of_eq
    (show z = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (centre z)) L)) ≫ X.fromSpecStalk (centre z)
      from (LieTangent.spec_centre z).symm) Mz
  let j : T →ₗ[X.presheaf.stalk (centre z)] V :=
    { toFun := β
      map_add' := map_add β
      map_smul' := fun a t => hsβ a t }
  have hbc : IsBaseChange L j := (GlobalTheory.T.lie_model_finite_base_change X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) T M0).2.2
    L V M' j fun t => by
      rw [hM']
      exact congrArg (fun w => w.left) (hβ t)
  refine ⟨T, iT, mT, M0, i, β, hext, hβ, hsi, hsβ, honto, fun ψ hψ => ?_, fun P hP => ?_⟩
  · let ψl : T →ₗ[X.presheaf.stalk (centre z)] L :=
      { toFun := ψ
        map_add' := map_add ψ
        map_smul' := fun a t => by
          rw [hψ, RingHom.id_apply, Algebra.smul_def]
          rfl }
    exact ⟨hbc.lift ψl, fun t => hbc.lift_eq ψl t⟩
  · refine eq_top_iff.2 fun x _ => ?_
    exact hbc.inductionOn x (· ∈ P) P.zero_mem hP (fun c n hn => P.smul_mem c hn) (fun _ _ => P.add_mem)

theorem value_end [IsCommMonObj G] {Li T : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (hξ : IsCptGen ξ) {L : Type} [Field L] (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {V : Type} [AddCommGroup V]
    [Module L V] (Mz : LieModel G z V) [AddCommGroup T] [Module (X.presheaf.stalk (centre z)) T]
    (M0 : LieModel (R := X.presheaf.stalk (centre z)) G (X.fromSpecStalk (centre z)) T) (i : T →+ Li) (β : T →+ V)
    (hext : ∀ t, M.Extends ⟨centre z, h⟩ (i t) (M0.pt t))
    (hβ : ∀ t, Mz.pt (β t) = LieTangent.epsBase _ (LieTangent.spec_centre z) ≫ M0.pt t)
    (f : G ⟶ G) [IsMonHom f] (t t' : T) (e : M.pt (i t) ≫ f = M.pt (i t')) :
    Mz.pt (β t) ≫ f = Mz.pt (β t') := by
  have h1 : M.Extends ⟨centre z, h⟩ (i t') (M0.pt t ≫ f) := by
    have h0 := (M.extends_iff _ _ _).1 (hext t)
    refine (M.extends_iff _ _ _).2 ⟨?_, ?_⟩
    · have h2 := h0.1
      rw [LieTangent.isTanAt_iff] at h2 ⊢
      rw [← Category.assoc, h2, MonObj.one_comp]
    · rw [← e, h0.2, Category.assoc]
  have h2 := (hext t').unique (hξ.inj _) h1
  rw [hβ, hβ, h2, Category.assoc]

end Stalk

theorem not_inFibre {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {L : Type} [Field L] [CharZero L]
    (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) (r : ℕ) (hr : r.Prime) : ¬ InFibre ξ r ⟨centre z, h⟩ := by
  have hu : IsUnit ((r : X.presheaf.stalk (centre z))) := by
    have hv : IsUnit ((Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z))) := by
      rw [map_natCast]
      exact (Nat.cast_ne_zero.2 hr.ne_zero).isUnit
    haveI : IsLocalHom (Scheme.stalkClosedPointTo z).hom :=
      inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
    exact isUnit_of_map_unit _ _ hv
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have h1 : (r : Ω) * genMap ξ ⟨centre z, h⟩ g = 1 := by
    have := congrArg (genMap ξ ⟨centre z, h⟩) hg
    rwa [map_mul, map_natCast, map_one] at this
  have h0 : (r : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact not_not.2 ⟨h0, natCast_mem _ _, ⟨g, eq_inv_of_mul_eq_one_right h1⟩⟩

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F} {Y : Model Xo c β₀} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem values_core (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] (z : Sp L ⟶ 𝔐.X) (tK : SAB H (Sp L))
    (mp : SABMap tK 𝔐.t z) {V : Type} [AddCommGroup V] [Module L V] (MV : LieModel tK.G (𝟙 (Sp L)) V)
    (ρ : 𝓞 E →+* Module.End L V) (σ : CMType H ⊕ CMType H → (𝓞 E →+* L)) (hσ : Function.Injective σ)
    (hact : MV.IsActOf tK.act.act ρ) (hlab : 𝔐.LabVal z id σ)
    (hlat : 𝔐.M.lat ⟨centre z, 𝔐.all _⟩ = ⨆ s, 𝔐.dR s ⟨centre z, 𝔐.all _⟩)
    (lab : CMType H ⊕ CMType H) {m : ℕ} (s : Fin m → 𝔐.Li) (hfr : (𝔐.dR lab).IsFrameAt s ⟨centre z, 𝔐.all _⟩) :
    ∃ sL : Fin m → V, (∀ k, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (s k) v ∧ (MV.pt (sL k)).left ≫ mp.φ = v.left) ∧
      LinearIndependent L sL ∧ Submodule.span L (Set.range sL) = eigSp ρ (σ lab) := by
  classical
  haveI := 𝔐.t.semi.smooth
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  let q : Cpt 𝔐.ξ := ⟨centre z, 𝔐.all _⟩
  obtain ⟨M₁, hM₁⟩ := (LiePull.lieModel_pullback _ _ 𝔐.t.G tK.G z mp.φ mp.cart L (𝟙 _) V).2 MV
  obtain ⟨Mz, hMz⟩ := exists_model_of_eq (Category.id_comp z) M₁
  have hM : ∀ e, (MV.pt e).left ≫ mp.φ = (Mz.pt e).left := fun e => (hM₁ e).trans (hMz e).symm
  obtain ⟨T, iT, mT, M0, i, β, hext, hβ, hsi, hsβ, honto, hlift, hgen⟩ := stalk_model 𝔐.M hξ z (𝔐.all _) Mz
  have hilat : ∀ t, i t ∈ 𝔐.M.lat q := fun t => (𝔐.M.mem_lat_iff q _).2 ⟨_, hext t⟩
  have hinj : Function.Injective i := fun t t' e =>
    M0.inj ((hext t).unique (hξ.inj q) (by rw [e]; exact hext t'))
  have hemb : Function.Injective 𝔐.emb := fun a b e => hσ (RingHom.ext fun x => by
    have h2 := hlab b x
    have h1 := hlab a x
    simp only [id] at h1 h2
    rw [← e] at h2
    exact LieTangent.valAt_unique hξ h1 h2)
  have hVg := iSupIndep_eigSp 𝔐.ρ 𝔐.emb hemb
  have hW := iSupIndep_eigSp ρ σ hσ
  have hs_mem : ∀ k, s k ∈ 𝔐.dR lab q := fun k => by
    rw [show 𝔐.dR lab q = _ from hfr.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose b hb using fun k => honto (s k) (hs_mem k).1
  have hdec : ∀ t, ∃ f : CMType H ⊕ CMType H → T, (∀ j, i (f j) ∈ eigSp 𝔐.ρ (𝔐.emb j)) ∧ t = ∑ j, f j := by
    intro t
    have h1 := hilat t
    rw [show 𝔐.M.lat q = _ from hlat] at h1
    obtain ⟨f, hf, e⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 h1
    rw [Finsupp.sum_fintype _ _ fun _ => rfl] at e
    choose g hg using fun j => honto (f j) (hf j).1
    refine ⟨g, fun j => ?_, hinj ?_⟩
    · rw [hg]
      exact (hf j).2
    · rw [map_sum, ← e]
      exact (Finset.sum_congr rfl fun j _ => hg j).symm
  have hβW : ∀ j t, i t ∈ eigSp 𝔐.ρ (𝔐.emb j) → β t ∈ eigSp ρ (σ j) := by
    intro j t ht
    refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker]
    obtain ⟨h1, u, hu1, hu2⟩ := hlab j a
    have he : 𝔐.ρ a (i t) = 𝔐.emb j a • i t := by
      have := (Submodule.mem_iInf _).1 ht a
      simpa [sub_eq_zero] using this
    have e1 : 𝔐.M.pt (i t) ≫ 𝔐.t.act.act a = 𝔐.M.pt (i (u • t)) := by
      refine (𝔐.act a (i t)).symm.trans (congrArg 𝔐.M.pt ?_)
      rw [he, hsi]
      exact congrArg (· • i t) hu1.symm
    haveI := 𝔐.t.act.hom a
    have e2 := value_end 𝔐.M hξ z (𝔐.all _) Mz M0 i β hext hβ (𝔐.t.act.act a) t (u • t) e1
    have e3 : ρ a (β t) = σ j a • β t := Mz.inj (Over.OverMorphism.ext (by
      rw [← hM, hact a (β t), Over.comp_left, Category.assoc, mp.act a, ← Category.assoc, hM, ← Over.comp_left, e2,
        hsβ]
      exact congrArg (fun x => (Mz.pt (x • β t)).left) hu2))
    simp [e3]
  obtain ⟨hli, hspan⟩ := values_basis (genMap 𝔐.ξ q) (hξ.inj q) (Scheme.stalkClosedPointTo z).hom i hsi β hsβ hlift hgen
    (fun j => eigSp 𝔐.ρ (𝔐.emb j)) hVg (fun j => eigSp ρ (σ j)) hW hdec hβW lab b
    (by simpa [hb] using hfr.1) (fun k => by rw [hb]; exact (hs_mem k).2) (fun t ht => by
      have hm : i t ∈ 𝔐.dR lab q := ⟨hilat t, ht⟩
      rw [show 𝔐.dR lab q = _ from hfr.2] at hm
      obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
      choose r hr using fun k => RingHom.mem_range.1 (cf k).2
      refine ⟨r, hinj ?_⟩
      rw [← hcf, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsi, hr, hb]
      rfl)
  refine ⟨fun k => β (b k), fun k => ⟨Mz.pt (β (b k)), ?_, hM _⟩, hli, hspan⟩
  exact (𝔐.M.valAt_iff _ _ _).2 ⟨𝔐.all _, M0.pt (b k), by rw [← hb k]; exact hext _, hβ _⟩

end Core

theorem values_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H ⊕ CMType H) (m : ℕ) (s : Fin m → 𝔐.Li), 𝔐.IsLinPtOf z P MV A → (𝔐.dR lab).IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ → ∃ sL : Fin m → V, IsValues 𝔐 z P MV s sL ∧ LinearIndependent L sL ∧ Submodule.span L (Set.range sL) = eigSp A.ρ (A.σ lab) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P V _ _ _ _ MV A lab m s hLin hfr
  obtain ⟨hact, hlab, -⟩ := hLin
  have hlat := (GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐
    (FaithfulSMul.algebraMap_injective _ _) ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩
    (fun r hr => not_inFibre _ _ r hr)).2.2
  exact values_core 𝔐 _ P.tK P.m MV A.ρ A.σ A.σ_bij.1 hact hlab hlat lab s hfr

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FrameVal
