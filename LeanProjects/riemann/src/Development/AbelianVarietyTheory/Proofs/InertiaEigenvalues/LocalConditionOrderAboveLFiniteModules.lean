import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLCoeffMapFunctorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerFunctorLeftExactTorsionCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BkOnLeMapOfSurjectiveStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.LocCountFinite

theorem card_of_exact {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (h : Function.Exact f g) (hg : Function.Surjective g) : Nat.card B = Nat.card A * Nat.card C := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), Nat.card_congr (g.quotKerEquivOfSurjective hg).toEquiv,
    h.linearMap_ker_eq, ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv]

section Abstract

variable {R Γ M' M M'' : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup M''] [Module R M''] [TopologicalSpace M''] [DiscreteTopology M'']
  (ρ' : Representation R Γ M') (ρ : Representation R Γ M) (ρ'' : Representation R Γ M'')

abbrev coc (L : Submodule R (H1 ρ)) : Submodule R (Z1 ρ) := L.comap (Submodule.mkQ _)

theorem card_coc (hc : ContAction ρ) (L : Submodule R (H1 ρ)) :
    Nat.card (coc ρ L) * Nat.card (H0 ρ) = Nat.card L * Nat.card M := by
  let B := (B1 ρ).comap (Z1 ρ).subtype
  have hB : B ≤ coc ρ L := fun z hz => by
    have : (Submodule.Quotient.mk z : H1 ρ) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hz
    change (Submodule.Quotient.mk z : H1 ρ) ∈ L
    rw [this]; exact L.zero_mem
  have h1 : Nat.card (coc ρ L) = Nat.card B * Nat.card L := by
    refine card_of_exact (Submodule.inclusion hB) ((Submodule.mkQ B).restrict (p := coc ρ L) (q := L) fun _ h => h)
      (Submodule.inclusion_injective _) (fun z => ?_) (fun x => ?_)
    · constructor
      · intro hz
        exact ⟨⟨z.1, (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hz)⟩, rfl⟩
      · rintro ⟨b, rfl⟩
        exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 b.2)
    · obtain ⟨x, hx⟩ := x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨⟨z, hx⟩, rfl⟩
  have h2 : Nat.card M = Nat.card (H0 ρ) * Nat.card B := by
    refine card_of_exact (H0 ρ).subtype
      (((d0 ρ).codRestrict (Z1 ρ) fun m => coboundaries_le_cocycles ρ hc ⟨m, rfl⟩).codRestrict B fun m => ⟨m, rfl⟩)
      (Submodule.subtype_injective _) (fun m => ?_) (fun x => ?_)
    · constructor
      · intro hm
        refine ⟨⟨m, (mem_riemannRochSpace_iff_regularAt_everywhere ρ m).2 fun g => ?_⟩, rfl⟩
        have : ρ g m - m = 0 := congrFun (congrArg (fun z => z.1.1) hm) g
        exact sub_eq_zero.1 this
      · rintro ⟨b, rfl⟩
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        exact sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere ρ _).1 b.2 g)
    · obtain ⟨⟨z, hz⟩, m, hm⟩ := x
      exact ⟨m, Subtype.ext (Subtype.ext hm)⟩
  rw [h1, h2]; ring

theorem card_coc_mul (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hinj : Function.Injective u)
    (w : M →ₗ[R] M'') (hw : ∀ g m, w (ρ g m) = ρ'' g (w m)) (hex : Function.Exact u w) (hsurj : Function.Surjective w)
    (hc : ContAction ρ) (L' : Submodule R (H1 ρ')) (L : Submodule R (H1 ρ)) (L'' : Submodule R (H1 ρ''))
    (h1 : ∀ x, mapH1 ρ' ρ u continuous_of_discreteTopology hu x ∈ L ↔ x ∈ L')
    (h2 : ∀ x ∈ L, mapH1 ρ ρ'' w continuous_of_discreteTopology hw x ∈ L'')
    (h3 : L'' ≤ L.map (mapH1 ρ ρ'' w continuous_of_discreteTopology hw)) :
    Nat.card (coc ρ L) = Nat.card (coc ρ' L') * Nat.card (coc ρ'' L'') := by
  refine card_of_exact
    ((cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu).restrict (p := coc ρ' L') (q := coc ρ L) fun z h => (h1 _).2 h)
    ((cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw).restrict (p := coc ρ L) (q := coc ρ'' L'') fun z h => h2 _ h)
    (fun a b h => Subtype.ext (Subtype.ext (funext fun g => hinj (congrFun (congrArg (fun z => z.1.1) h) g))))
    (fun z => ?_) (fun x => ?_)
  · constructor
    · intro hz
      have e1 : ∀ g, u (Function.invFun u (z.1.1 g)) = z.1.1 g := fun g =>
        Function.invFun_eq ((hex _).1 (congrFun (congrArg (fun z => z.1.1) hz) g))
      let z' : Z1 ρ' := ⟨fun g => Function.invFun u (z.1.1 g),
        (continuous_of_discreteTopology (f := Function.invFun u)).comp z.1.2.1, fun g h => hinj (by
          rw [map_add, hu, e1, e1, e1]
          exact z.1.2.2 g h)⟩
      have e : cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z' = z.1 := Subtype.ext (funext e1)
      refine ⟨⟨z', (h1 _).1 ?_⟩, Subtype.ext e⟩
      change Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z') ∈ L
      rw [e]; exact z.2
    · rintro ⟨b, rfl⟩
      exact Subtype.ext (Subtype.ext (funext fun g => hex.apply_apply_eq_zero _))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy, e⟩ := h3 hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have e' : (Submodule.Quotient.mk (x - cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw z) : H1 ρ'') = 0 := by
      rw [Submodule.Quotient.mk_sub, sub_eq_zero]
      exact e.symm
    obtain ⟨m, hm⟩ := (GlobalTheory.SelLeftExact.mk_eq_zero_iff ρ'' _).1 e'
    obtain ⟨m, rfl⟩ := hsurj m
    let b : Z1 ρ := ⟨d0 ρ m, coboundaries_le_cocycles ρ hc ⟨m, rfl⟩⟩
    have hb : (Submodule.Quotient.mk b : H1 ρ) = 0 := (GlobalTheory.SelLeftExact.mk_eq_zero_iff ρ b).2 ⟨m, fun _ => rfl⟩
    refine ⟨⟨z + b, ?_⟩, Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    · change (Submodule.Quotient.mk (z + b) : H1 ρ) ∈ L
      rw [Submodule.Quotient.mk_add, hb, add_zero]
      exact hy
    · change w (z.1 g + (ρ g m - m)) = x.1 g
      have : x.1 g - w (z.1 g) = ρ'' g (w m) - w m := hm g
      rw [map_add, map_sub, hw, ← this]
      abel

theorem card_six [Finite M] (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hinj : Function.Injective u)
    (w : M →ₗ[R] M'') (hw : ∀ g m, w (ρ g m) = ρ'' g (w m)) (hex : Function.Exact u w) (hsurj : Function.Surjective w)
    (hc' : ContAction ρ') (hc : ContAction ρ) (hc'' : ContAction ρ'')
    (L' : Submodule R (H1 ρ')) (L : Submodule R (H1 ρ)) (L'' : Submodule R (H1 ρ''))
    (h1 : ∀ x, mapH1 ρ' ρ u continuous_of_discreteTopology hu x ∈ L ↔ x ∈ L')
    (h2 : ∀ x ∈ L, mapH1 ρ ρ'' w continuous_of_discreteTopology hw x ∈ L'')
    (h3 : L'' ≤ L.map (mapH1 ρ ρ'' w continuous_of_discreteTopology hw)) :
    Nat.card L * (Nat.card (H0 ρ') * Nat.card (H0 ρ'')) = Nat.card (H0 ρ) * (Nat.card L' * Nat.card L'') := by
  have a := card_coc ρ hc L
  have a' := card_coc ρ' hc' L'
  have a'' := card_coc ρ'' hc'' L''
  have b := card_coc_mul ρ' ρ ρ'' u hu hinj w hw hex hsurj hc L' L L'' h1 h2 h3
  have c := card_of_exact u w hinj hex hsurj
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := M)) ?_
  calc _ = (Nat.card L * Nat.card M) * (Nat.card (H0 ρ') * Nat.card (H0 ρ'')) := by ring
    _ = Nat.card (H0 ρ) * ((Nat.card (coc ρ' L') * Nat.card (H0 ρ')) * (Nat.card (coc ρ'' L'') * Nat.card (H0 ρ''))) := by
      rw [← a, b]; ring
    _ = _ := by rw [a', a'', c]; ring

theorem contAction_sub (hc : ContAction ρ) (U : Subgroup Γ) : ContAction (ρ.comp U.subtype) :=
  hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

end Abstract

theorem tors_of_finite (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (B : Type) [AddCommGroup B] [Module A B] :
    Tors A B := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine fun b => ⟨n, fun x hx => ?_⟩
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

theorem finite_places (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l ≠ 0) : (placesOver F l).Finite := by
  have h : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    simpa using hl
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem locCountFin : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → LocSat bkP i s κ → LocCount bkP i s κ → LocCountFin bkP i s κ := by
  intro D N X bkP i s A _ _ _ _ κ Q hS hK hL hC Y _ _ _ _ _
  haveI := hS.2.1
  have hfin := finite_places D.host.E (X.l i) (Fact.out : (X.l i).Prime).ne_zero
  have hcont : ∀ (B : Type) [AddCommGroup B] [Module A B] [TopologicalSpace B] [DiscreteTopology B] (v : PlE D.host),
      ContAction ((repOn (Tgl i s) κ B).comp (DecV N v).subtype) := fun B _ _ _ _ v =>
    contAction_sub _ (GlobalTheory.SelLeftExact.contAction_of_tors (X.twistBaseCoefficientRing_isAdic i) _ (GlobalTheory.SelLeftExact.continuous_Tgl i s) κ
      hS.2.2.2.1 (tors_of_finite A B)) _
  induction hn : Nat.card Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
  subst hn
  rcases subsingleton_or_nontrivial Y with hY | hY
  · have e1 : ∀ v, Nat.card (bkOn bkP i (Tgl i s) κ Y v) = 1 := fun v => by
      haveI : Subsingleton (H1 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      exact Nat.card_unique
    have e2 : ∀ v, Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) = 1 := fun v => Nat.card_unique
    have e3 : Nat.card Y = 1 := Nat.card_unique
    simp only [e1, e2, e3, one_pow, mul_one]
  · obtain ⟨K, hKa, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule A Y)).resolve_left top_ne_bot
    have hKs : IsSimpleModule A K := isSimpleModule_iff_isAtom.2 hKa
    letI : TopologicalSpace (Y ⧸ K) := ⊥
    haveI : DiscreteTopology (Y ⧸ K) := ⟨rfl⟩
    haveI : Finite (Y ⧸ K) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective K)
    have hex : Function.Exact K.subtype K.mkQ := LinearMap.exact_subtype_mkQ K
    have hcard := card_of_exact K.subtype K.mkQ K.subtype_injective hex K.mkQ_surjective
    have hlt : Nat.card (Y ⧸ K) < Nat.card Y := by
      haveI := IsSimpleModule.nontrivial A K
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      have h2 : 0 < Nat.card (Y ⧸ K) := Nat.card_pos
      rw [hcard]
      nlinarith
    have a := hC K hKs
    have b := ih _ hlt (Y ⧸ K) rfl
    have c : ∀ v ∈ hfin.toFinset, Nat.card (bkOn bkP i (Tgl i s) κ Y v) *
        (Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype)) *
          Nat.card (H0 ((repOn (Tgl i s) κ (Y ⧸ K)).comp (DecV N v).subtype))) =
        Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) *
          (Nat.card (bkOn bkP i (Tgl i s) κ K v) * Nat.card (bkOn bkP i (Tgl i s) κ (Y ⧸ K) v)) := fun v hv => by
      have hv' := hfin.mem_toFinset.1 hv
      refine card_six _ _ _ (K.subtype.compLeft (Fin D.R.r)) (fun g m => repOn_map (Tgl i s) κ K.subtype g.1 m)
        (fun x y h => funext fun a => Subtype.ext (congrFun h a)) (K.mkQ.compLeft (Fin D.R.r))
        (fun g m => repOn_map (Tgl i s) κ K.mkQ g.1 m) (fun m => ⟨fun hm => ?_, ?_⟩) (fun m => ?_)
        (hcont _ v) (hcont _ v) (hcont _ v) _ _ _
        (fun x => ⟨hL v hv' K Y (tors_of_finite A Y) K.subtype K.subtype_injective x,
          localConditionAboveL_coeffMap_functorial bkP i _ κ K.subtype v x⟩)
        (localConditionAboveL_coeffMap_functorial bkP i _ κ K.mkQ v)
        (GlobalTheory.T.bkOn_le_map_h1MapSubgroup_of_surjective D N X bkP i s A κ Q hS hK Y (Y ⧸ K) K.mkQ K.mkQ_surjective v)
      · choose m' hm' using fun a => (hex (m a)).1 (congrFun hm a)
        exact ⟨m', funext hm'⟩
      · rintro ⟨m', rfl⟩
        exact funext fun a => hex.apply_apply_eq_zero _
      · choose m' hm' using fun a => K.mkQ_surjective (m a)
        exact ⟨m', funext hm'⟩
    have c' := Finset.prod_congr rfl c
    simp only [Finset.prod_mul_distrib] at c'
    simp only [finprod_mem_eq_finite_toFinset_prod _ hfin] at a b ⊢
    rw [a, b] at c'
    have hpos : 0 < (∏ v ∈ hfin.toFinset, Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype))) *
        ∏ v ∈ hfin.toFinset, Nat.card (H0 ((repOn (Tgl i s) κ (Y ⧸ K)).comp (DecV N v).subtype)) :=
      Nat.mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (Finset.prod_pos fun v _ => Nat.card_pos)
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [c', hcard, mul_pow]
    ring

end GlobalTheory.LocCountFinite
