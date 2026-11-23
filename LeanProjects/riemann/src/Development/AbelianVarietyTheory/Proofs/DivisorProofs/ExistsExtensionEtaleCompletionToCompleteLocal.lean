import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

open IsLocalRing GlobalTheory.Toroidal

namespace GlobalTheory.EtaleCompletionLift

section Etale

variable {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing S] [IsLocalRing S]
  [IsNoetherianRing S] [Algebra O S]

omit [IsNoetherianRing O] in

theorem finite_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Finite O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Module.Finite O (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  rw [Ideal.map_pow, hm]
  have hle : maximalIdeal S ^ (n + 1) ≤ maximalIdeal S := Ideal.pow_le_self n.succ_ne_zero
  refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.factorₐ O hle)
    (Ideal.Quotient.factor_surjective hle) ?_ (IsNoetherian.noetherian _)
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : x ∈ maximalIdeal S := Ideal.Quotient.eq_zero_iff_mem.1 hx
  exact mem_nilradical.2 ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hx' _⟩

omit [IsNoetherianRing O] in

theorem formallyUnramified_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Algebra.FormallyUnramified O (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  have := finite_quotient hm n
  set J := (maximalIdeal O ^ (n + 1)).map (algebraMap O S) with hJ
  have hle : J ≤ maximalIdeal S := by
    rw [hJ, Ideal.map_pow, hm]; exact Ideal.pow_le_self n.succ_ne_zero
  have : Nontrivial (S ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hle
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmk : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal S).map (Ideal.Quotient.mk J) = maximalIdeal (S ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have H : (maximalIdeal O).map (algebraMap O (S ⧸ J)) = maximalIdeal (S ⧸ J) := by
    rw [← hmap, ← hm, Ideal.map_map]; rfl
  have : IsLocalHom (algebraMap O (S ⧸ J)) :=
    ((local_hom_TFAE (algebraMap O (S ⧸ J))).out 2 0 rfl rfl).mp H.le
  let g : (S ⧸ maximalIdeal S) →ₐ[O] ResidueField (S ⧸ J) :=
    Ideal.Quotient.liftₐ _ ((IsScalarTower.toAlgHom O (S ⧸ J) (ResidueField (S ⧸ J))).comp (Ideal.Quotient.mkₐ O J))
      fun a ha => by
        change residue (S ⧸ J) (Ideal.Quotient.mk J a) = 0
        rw [residue_eq_zero_iff, ← hmap]
        exact Ideal.mem_map_of_mem _ ha
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨x, rfl⟩ := residue_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have : Algebra.FormallyUnramified O (ResidueField (S ⧸ J)) := .of_surjective g hg
  have : Algebra.FormallyUnramified (ResidueField O) (ResidueField (S ⧸ J)) := .of_restrictScalars O _ _
  have : Module.Finite O (ResidueField (S ⧸ J)) := .of_surjective g.toLinearMap hg
  have : Module.Finite (ResidueField O) (ResidueField (S ⧸ J)) := .of_restrictScalars_finite O _ _
  have : Algebra.IsSeparable (ResidueField O) (ResidueField (S ⧸ J)) := Algebra.FormallyUnramified.isSeparable _ _
  exact Algebra.FormallyUnramified.of_map_maximalIdeal H

theorem etale_quotient (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S) [Module.Flat O S]
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ) :
    Algebra.Etale (O ⧸ maximalIdeal O ^ (n + 1)) (S ⧸ (maximalIdeal O ^ (n + 1)).map (algebraMap O S)) := by
  have := finite_quotient hm n
  have := formallyUnramified_quotient hm n
  set I := maximalIdeal O ^ (n + 1)
  have : Module.Finite (O ⧸ I) (S ⧸ I.map (algebraMap O S)) := .of_restrictScalars_finite O _ _
  have : Algebra.FormallyUnramified (O ⧸ I) (S ⧸ I.map (algebraMap O S)) := .of_restrictScalars O _ _
  have : Algebra.FinitePresentation (O ⧸ I) (S ⧸ I.map (algebraMap O S)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Flat (O ⧸ I) (S ⧸ I.map (algebraMap O S)) :=
    .of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  exact .of_formallyUnramified_of_flat

theorem existsUnique_lift (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S) [Module.Flat O S]
    [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)] (n : ℕ)
    {B : Type} [CommRing B] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0) (K : Ideal B)
    (hK : IsNilpotent K) (g : S →+* B ⧸ K) (hg : g.comp (algebraMap O S) = (Ideal.Quotient.mk K).comp χ) :
    ∃! F : S →+* B, F.comp (algebraMap O S) = χ ∧ (Ideal.Quotient.mk K).comp F = g := by
  have := etale_quotient hm n
  set I := maximalIdeal O ^ (n + 1)
  letI : Algebra (O ⧸ I) B := (Ideal.Quotient.lift I χ hχ).toAlgebra
  have desc : ∀ {C : Type} [CommRing C] [Algebra (O ⧸ I) C] (f : S →+* C),
      (∀ x, f (algebraMap O S x) = algebraMap (O ⧸ I) C (Ideal.Quotient.mk I x)) →
      ∃ f' : (S ⧸ I.map (algebraMap O S)) →ₐ[O ⧸ I] C, ∀ x, f' (Ideal.Quotient.mk _ x) = f x := by
    intro C _ _ f hf
    have h0 : I.map (algebraMap O S) ≤ RingHom.ker f := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change f (algebraMap O S x) = 0
      rw [hf, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    refine ⟨⟨Ideal.Quotient.lift _ f fun a ha => h0 ha, fun r => ?_⟩, fun x => rfl⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact hf r
  obtain ⟨g', hg'⟩ := desc g fun x => congr($hg x)
  let F := Algebra.FormallySmooth.lift K hK g'
  refine ⟨F.toRingHom.comp (Ideal.Quotient.mk _), ⟨RingHom.ext fun x => ?_, RingHom.ext fun x => ?_⟩, ?_⟩
  · exact F.commutes (Ideal.Quotient.mk I x)
  · exact (Algebra.FormallySmooth.mk_lift K hK g' _).trans (hg' x)
  · rintro G ⟨h1, h2⟩
    obtain ⟨G', hG'⟩ := desc G fun x => congr($h1 x)
    have : G' = F := Algebra.FormallyUnramified.ext K hK fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Algebra.FormallySmooth.mk_lift K hK g', hg', hG']
      exact congr($h2 x)
    ext x
    rw [← hG', this]
    rfl

theorem existsUnique_lift_of_surjective (hm : (maximalIdeal O).map (algebraMap O S) = maximalIdeal S)
    [Module.Flat O S] [Module.Finite O (S ⧸ maximalIdeal S)] [Algebra.FormallyUnramified O (S ⧸ maximalIdeal S)]
    (n : ℕ) {B C : Type} [CommRing B] [CommRing C] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0)
    (w : B →+* C) (hw : Function.Surjective w) (hK : IsNilpotent (RingHom.ker w)) (g : S →+* C)
    (hg : g.comp (algebraMap O S) = w.comp χ) :
    ∃! F : S →+* B, F.comp (algebraMap O S) = χ ∧ w.comp F = g := by
  let e := RingHom.quotientKerEquivOfSurjective hw
  have := existsUnique_lift hm n χ hχ _ hK (e.symm.toRingHom.comp g) (by
    ext x
    exact e.symm_apply_eq.2 congr($hg x))
  refine (existsUnique_congr fun F => and_congr Iff.rfl ?_).1 this
  simp only [RingHom.ext_iff]
  exact forall_congr' fun x => e.eq_symm_apply

end Etale

theorem existsUnique_lift_of_isEtaleCompletion {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {φ : O →+* S} (h : IsEtaleCompletion φ)
    (hun : ((residue S).comp φ).FormallyUnramified)
    (n : ℕ) {B C : Type} [CommRing B] [CommRing C] (χ : O →+* B) (hχ : ∀ x ∈ maximalIdeal O ^ (n + 1), χ x = 0)
    (w : B →+* C) (hw : Function.Surjective w) (hK : IsNilpotent (RingHom.ker w)) (g : S →+* C)
    (hg : g.comp φ = w.comp χ) :
    ∃! F : S →+* B, F.comp φ = χ ∧ w.comp F = g := by
  obtain ⟨hfl, hm, hfin⟩ := h
  letI := φ.toAlgebra
  have : Module.Flat O S := hfl
  have : Module.Finite O (S ⧸ maximalIdeal S) := RingHom.finite_algebraMap.1 hfin
  have : Algebra.FormallyUnramified O (S ⧸ maximalIdeal S) := RingHom.formallyUnramified_algebraMap.1 hun
  exact existsUnique_lift_of_surjective hm n χ hχ w hw hK g hg

theorem isNilpotent_ker {E C : Type} [CommRing E] [CommRing C] {I : Ideal E} {v : E →+* C} (hv : RingHom.ker v = I)
    (n : ℕ) (w : E ⧸ I ^ (n + 1) →+* C) (hw : ∀ x, w (Ideal.Quotient.mk _ x) = v x) :
    IsNilpotent (RingHom.ker w) := by
  have : RingHom.ker w ≤ I.map (Ideal.Quotient.mk (I ^ (n + 1))) := fun x hx => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hv, RingHom.mem_ker, ← hw]
    exact hx
  refine ⟨n + 1, le_bot_iff.1 ((Ideal.pow_right_mono this _).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem exists_extension_of_surjective {O S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {φ : O →+* S} (het : IsEtaleCompletion φ)
    (hun : ((residue S).comp φ).FormallyUnramified) {E C : Type} [CommRing E] [CommRing C] (m : Ideal E)
    [IsAdicComplete m E] (ψ : O →+* E) (h1 : (maximalIdeal O).map ψ ≤ m) (v : E →+* C) (hs : Function.Surjective v)
    (hv : RingHom.ker v = m) (u : S →+* C) (hc : u.comp φ = v.comp ψ) :
    ∃ b : S →+* E, b.comp φ = ψ ∧ v.comp b = u := by
  have hle : ∀ n : ℕ, m ^ (n + 1) ≤ RingHom.ker v := fun n => (Ideal.pow_le_self n.succ_ne_zero).trans hv.ge
  obtain ⟨w, hw⟩ : ∃ w : ∀ n : ℕ, E ⧸ m ^ (n + 1) →+* C, ∀ n x, w n (Ideal.Quotient.mk _ x) = v x :=
    ⟨fun n => Ideal.Quotient.lift _ v fun a ha => hle n ha, fun n x => Ideal.Quotient.lift_mk _ _ _⟩
  have hws : ∀ n, Function.Surjective (w n) := fun n y => by
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨_, hw n x⟩
  have key : ∀ n, ∃! F : S →+* E ⧸ m ^ (n + 1),
      F.comp φ = (Ideal.Quotient.mk _).comp ψ ∧ (w n).comp F = u := fun n => by
    refine existsUnique_lift_of_isEtaleCompletion het hun n _ (fun x hx => ?_) _ (hws n)
      (isNilpotent_ker hv n _ (hw n)) _ ?_
    · rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.pow_right_mono h1 _ ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    · ext x
      rw [hc, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hw]
  choose F hF hU using key
  have hF1 : ∀ n x, F n (φ x) = Ideal.Quotient.mk _ (ψ x) := fun n x => RingHom.congr_fun (hF n).1 x
  have hF2 : ∀ n x, w n (F n x) = u x := fun n x => RingHom.congr_fun (hF n).2 x
  have ha : StrictMono (fun n : ℕ => n + 1) := strictMono_id.add_const 1
  have hcomp : ∀ {k : ℕ}, (Ideal.Quotient.factorPow m (ha.monotone k.le_succ)).comp (F (k + 1)) = F k := by
    intro k
    refine hU k _ ⟨RingHom.ext fun x => ?_, RingHom.ext fun x => ?_⟩
    · simp only [RingHom.comp_apply, hF1, Ideal.Quotient.factor_mk]
    · rw [← hF2 (k + 1), RingHom.comp_apply, RingHom.comp_apply]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (F (k + 1) x)
      rw [← hy, hw]
      exact (congrArg (w k) (Ideal.Quotient.factor_mk _ y)).trans (hw k y)
  obtain ⟨b, hb⟩ : ∃ b : S →+* E, ∀ n x, Ideal.Quotient.mk (m ^ (n + 1)) (b x) = F n x :=
    ⟨_, fun n x => IsAdicComplete.StrictMono.mk_liftRingHom m ha F hcomp x⟩
  refine ⟨b, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' m ha
    intro n x
    exact (hb n _).trans (hF1 n x)
  · ext x
    rw [RingHom.comp_apply, ← hw 0, hb, hF2]

theorem exists_extension : ∀ (O R' E Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R']
    [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [Field Ω] (φ' : O →+* R') (ψ : O →+* E)
    (u' : R' →+* Ω) (v : E →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified →
    IsAdicComplete (maximalIdeal E) E → IsLocalHom ψ → RingHom.ker u' = maximalIdeal R' →
    RingHom.ker v = maximalIdeal E → v.comp ψ = u'.comp φ' → (∀ r : R', u' r ∈ v.range) →
    ∃ b : R' →+* E, b.comp φ' = ψ ∧ v.comp b = u' := by
  intro O R' E Ω _ _ _ _ _ _ _ _ _ φ' ψ u' v het hun hE hψ _ hv hc hr
  obtain ⟨b, h1, h2⟩ := exists_extension_of_surjective het hun (maximalIdeal E) ψ
    (((local_hom_TFAE ψ).out 0 2 rfl rfl).mp hψ) v.rangeRestrict v.rangeRestrict_surjective
    (v.ker_rangeRestrict.trans hv) (u'.codRestrict v.range hr)
    (RingHom.ext fun x => Subtype.ext (RingHom.congr_fun hc x).symm)
  exact ⟨b, h1, RingHom.ext fun x => congrArg Subtype.val (RingHom.congr_fun h2 x)⟩

end GlobalTheory.EtaleCompletionLift
