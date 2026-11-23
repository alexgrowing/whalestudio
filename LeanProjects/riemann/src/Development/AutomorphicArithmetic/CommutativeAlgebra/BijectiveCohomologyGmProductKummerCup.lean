import Development.AutomorphicArithmetic.CommutativeAlgebra.InjectiveComplexProductSectionMapQuasiIso
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallySurjectiveMultiplicativeGroupKunnethMap
import Development.AutomorphicArithmetic.CommutativeAlgebra.PsiCommDifferentialOfCocycle
import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyClassInLSurjectiveAndInjective
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCocycleProductEqPullAddCup
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExteriorCupCocycleExistsOfPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

private theorem genK (W : Scheme.{0}) (I Q P : Cx R) [I.IsStrictlyGE 0] [Q.IsStrictlyGE 0]
    (hI : ∀ s, Injective (I.X s)) (hQ : ∀ s, Injective (Q.X s)) (μ : Pair Q P I)
    (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) (Z : Scheme.{0} → Prop) (hZ : ∀ {T' T : Scheme.{0}}, (T' ⟶ T) → Z T → Z T')
    (hS : ∀ (T : Scheme.{0}), Z T → ∀ (m n : ℤ) (h : m + 1 = n) (y : CohomologyClass ((chains R).obj (sch.obj (W ⨯ T))) I n),
      Loc T fun V g => ∃ (a : CohomologyClass ((chains R).obj (sch.obj V)) I n) (b : CohomologyClass ((chains R).obj (sch.obj V)) Q m),
        cpull ((chains R).map (sch.map (prod.snd : W ⨯ V ⟶ V))) I n a +
          μ.cup (sch.obj (W ⨯ V)) h (cpull ((chains R).map (sch.map (prod.snd : W ⨯ V ⟶ V))) Q m b)
            (cpull ((chains R).map (sch.map (prod.fst : W ⨯ V ⟶ W))) P 1 (CohomologyClass.mk κ)) =
        cpull ((chains R).map (sch.map (prod.map (𝟙 W) g))) I n y)
    (hJ : ∀ (T : Scheme.{0}), Z T → ∀ (m n : ℤ) (h : m + 1 = n) (a : CohomologyClass ((chains R).obj (sch.obj T)) I n)
      (b : CohomologyClass ((chains R).obj (sch.obj T)) Q m),
        cpull ((chains R).map (sch.map (prod.snd : W ⨯ T ⟶ T))) I n a +
          μ.cup (sch.obj (W ⨯ T)) h (cpull ((chains R).map (sch.map (prod.snd : W ⨯ T ⟶ T))) Q m b)
            (cpull ((chains R).map (sch.map (prod.fst : W ⨯ T ⟶ W))) P 1 (CohomologyClass.mk κ)) = 0 →
        Loc T fun V g => cpull ((chains R).map (sch.map g)) I n a = 0 ∧ cpull ((chains R).map (sch.map g)) Q m b = 0)
    (E : Spc) (hE : ∀ T : Scheme.{0}, Nonempty (Sx E 0 T) → Z T) (m n : ℤ) (h : m + 1 = n) :
    Function.Bijective fun p : CohomologyClass ((chains R).obj E) I n × CohomologyClass ((chains R).obj E) Q m =>
      cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) I n p.1 +
        μ.cup (sch.obj W ⨯ E) h (cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) Q m p.2)
          (cpull ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _)) P 1 (CohomologyClass.mk κ)) := by
  have hz : Sec.map (P.d 1 2) (sg κ) = 0 := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R W P 0 1 2 (by omega) (by omega)).2 κ).1
  have hmono := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1
  haveI := LL_ge I Q
  have key : ∀ (T : Scheme.{0}) (n' : ℤ) (a₁ : Sec (I.X n') T) (a₂ : Sec (Q.X (n' + -1)) T),
      psi W μ (sg κ) T n' (cc a₁ (n'.negOnePow • a₂)) = Sec.res (prod.snd : W ⨯ T ⟶ T) a₁ +
        μ.mul (W ⨯ T) (n' + -1) 1 n' (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) a₂) (Sec.res (prod.fst : W ⨯ T ⟶ W) (sg κ)) := by
    intro T n' a₁ a₂
    change Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ (cc a₁ (n'.negOnePow • a₂))) + n'.negOnePow • μ.mul (W ⨯ T) (n' + -1) 1 n' (by omega)
      (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ (cc a₁ (n'.negOnePow • a₂)))) (Sec.res (prod.fst : W ⨯ T ⟶ W) (sg κ)) = _
    rw [c₁_cc, c₂_cc]
    generalize n'.negOnePow = ε
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  obtain ⟨Φ, hΦ, hΦv⟩ := UpperTheory.injectiveComplex_productSection_map_quasiIso R W (LL I Q) I (LL_inj hI hQ) hI (psi W μ (sg κ))
    (fun g s a => psi_nat W μ _ g s a) (fun T s t a => UpperTheory.psi_comm_differential_of_cocycle R W μ _ hz T s t a) Z hZ
    (by
      intro T hT n' b hb
      obtain ⟨y, hy0, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (W ⨯ T) I (n' - 1) n' (n' + 1) (by omega) rfl).1 b hb
      have hsy : sg y = b := (hy0 _ (𝟙 _)).trans (res_id _)
      refine hmono _ _ _ (hS T hT (n' + -1) n' (by omega) (CohomologyClass.mk y)) ?_
      rintro V g ⟨a, b', e⟩
      obtain ⟨α₁, rfl⟩ := a.mk_surjective
      obtain ⟨α₂, rfl⟩ := b'.mk_surjective
      obtain ⟨β, hβ, hσ⟩ := UpperTheory.exists_cocycle_product_eq_pull_add_cup R W _ μ κ (by omega : n' + -1 + 1 = n') α₁ α₂
      have e2 : CohomologyClass.mk (β - zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.map (𝟙 W) g)))) y (zero_add n')) = 0 := by
        rw [CohomologyClass.mk_sub, hβ, e, sub_eq_zero]
        rfl
      obtain ⟨c, hc⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (W ⨯ V) I (n' - 1) n' (n' + 1) (by omega) rfl).2 _).2.1 e2
      refine ⟨cc (sg α₁) (n'.negOnePow • sg α₂), c, ?_, ?_⟩
      · apply LLsec_ext
        · rw [c₁_d, c₁_cc, map_zero]
          exact ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R V I (n' - 1) n' (n' + 1) (by omega) rfl).2 α₁).1
        · rw [c₂_d, c₂_cc, map_zero]
          have h0 := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R V Q (n' + -1 - 1) (n' + -1) (n' + 1 + -1) (by omega) (by omega)).2 α₂).1
          generalize n'.negOnePow = ε
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [sg, h0]
      · rw [key, ← hσ]
        have h3 : sg (β - zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.map (𝟙 W) g)))) y (zero_add n')) = Sec.map (I.d (n' - 1) n') c := hc.symm
        rw [sg_sub, sg_pull, hsy] at h3
        rw [← h3]
        abel)
    (by
      rintro T hT n' a ha ⟨c, hc⟩
      have h1 : Sec.map (I.d n' (n' + 1)) (c₁ a) = 0 := by rw [← c₁_d, ha, map_zero]
      have h2 : Sec.map (Q.d (n' + -1) (n' + 1 + -1)) (c₂ a) = 0 := by
        have := c₂_d n' (n' + 1) a
        rw [ha, map_zero] at this
        exact neg_eq_zero.1 this.symm
      have h2' : Sec.map (Q.d (n' + -1) (n' + 1 + -1)) (n'.negOnePow • c₂ a) = 0 := by
        generalize n'.negOnePow = ε
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [h2]
      obtain ⟨α₁, hα₁, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R T I (n' - 1) n' (n' + 1) (by omega) rfl).1 _ h1
      obtain ⟨α₂, hα₂, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R T Q (n' + -1 - 1) (n' + -1) (n' + 1 + -1) (by omega) (by omega)).1 _ h2'
      have hs₁ : sg α₁ = c₁ a := (hα₁ _ (𝟙 _)).trans (res_id _)
      have hs₂ : sg α₂ = n'.negOnePow • c₂ a := (hα₂ _ (𝟙 _)).trans (res_id _)
      obtain ⟨β, hβ, hσ⟩ := UpperTheory.exists_cocycle_product_eq_pull_add_cup R W _ μ κ (by omega : n' + -1 + 1 = n') α₁ α₂
      have ha' : a = cc (sg α₁) (n'.negOnePow • sg α₂) := by
        apply LLsec_ext
        · rw [c₁_cc, hs₁]
        · rw [c₂_cc, hs₂]
          generalize n'.negOnePow = ε
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
      have e0 : CohomologyClass.mk β = 0 := by
        refine ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (W ⨯ T) I (n' - 1) n' (n' + 1) (by omega) rfl).2 β).2.2 ⟨c, ?_⟩
        rw [← hc]
        change _ = sg β
        rw [hσ, ← key, ← ha']
      refine hmono _ _ _ (hJ T hT (n' + -1) n' (by omega) (CohomologyClass.mk α₁) (CohomologyClass.mk α₂) (by rw [← hβ, e0])) ?_
      rintro V g ⟨e₁, e₂⟩
      obtain ⟨y₁, hy₁⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R V I (n' - 1) n' (n' + 1) (by omega) rfl).2
        (zcomp (Cocycle.ofHom ((chains R).map (sch.map g))) α₁ (zero_add n'))).2.1 e₁
      obtain ⟨y₂, hy₂⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R V Q (n' - 1 + -1) (n' + -1) (n' + 1 + -1) (by omega) (by omega)).2
        (zcomp (Cocycle.ofHom ((chains R).map (sch.map g))) α₂ (zero_add (n' + -1)))).2.1 e₂
      change _ = sg _ at hy₁
      change _ = sg _ at hy₂
      rw [sg_pull, hs₁] at hy₁
      rw [sg_pull, hs₂] at hy₂
      refine ⟨cc y₁ (-(n'.negOnePow • y₂)), ?_⟩
      apply LLsec_ext
      · rw [c₁_d, c₁_cc, c₁_res, hy₁]
      · rw [c₂_d, c₂_cc, c₂_res]
        generalize n'.negOnePow = ε at hy₂ ⊢
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [hy₂])
    E hE
  have hf : ∀ (α₁ : Cocycle ((chains R).obj E) I n) (α₂ : Cocycle ((chains R).obj E) Q m),
      Φ n (CohomologyClass.mk (inL h α₁ α₂)) = cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) I n (CohomologyClass.mk α₁) +
        μ.cup (sch.obj W ⨯ E) h (cpull ((chains R).map (prod.snd : sch.obj W ⨯ E ⟶ E)) Q m (CohomologyClass.mk α₂))
          (cpull ((chains R).map (prod.fst : sch.obj W ⨯ E ⟶ _)) P 1 (CohomologyClass.mk κ)) := by
    intro α₁ α₂
    obtain ⟨β, hβ, hv⟩ := hΦv n (inL h α₁ α₂)
    rw [hβ]
    exact UpperTheory.exteriorCup_cocycle_exists_of_pairing R W μ κ h α₁ α₂ β hv
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hpp
    obtain ⟨α₁, rfl⟩ := a.mk_surjective
    obtain ⟨α₂, rfl⟩ := b.mk_surjective
    obtain ⟨α₁', rfl⟩ := a'.mk_surjective
    obtain ⟨α₂', rfl⟩ := b'.mk_surjective
    have h0 : Φ n (CohomologyClass.mk (inL h (α₁ - α₁') (α₂ - α₂'))) = 0 := by
      rw [hf, CohomologyClass.mk_sub, CohomologyClass.mk_sub, map_sub, map_sub, map_sub, AddMonoidHom.sub_apply]
      beta_reduce at hpp
      rw [sub_add_sub_comm, hpp, sub_self]
    have h1 := (hΦ n).1 (h0.trans (map_zero _).symm)
    obtain ⟨e₁, e₂⟩ := (UpperTheory.cohomologyClass_inL_surjective_and_injective R h).2 _ _ h1
    rw [CohomologyClass.mk_sub, sub_eq_zero] at e₁ e₂
    rw [e₁, e₂]
  · intro y
    obtain ⟨x, rfl⟩ := (hΦ n).2 y
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨α₁, α₂, e⟩ := (UpperTheory.cohomologyClass_inL_surjective_and_injective R h).1 x
    exact ⟨(CohomologyClass.mk α₁, CohomologyClass.mk α₂), by rw [e]; exact (hf α₁ α₂).symm⟩

end UpperTheory.Kun

private theorem UpperTheory.Kun.main (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E) (m j : ℤ) :
    Function.Bijective fun p : Ht q E (m + 1) (j + 1) × Ht q E m j =>
      pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
        cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2) (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q)) := by
  obtain ⟨κ, hκ⟩ := (kappa q).mk_surjective
  have hr := fun i : ℤ => GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  haveI := (hr (j + 1)).2.2.1
  haveI := (hr j).2.2.1
  have hmono := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1
  have h := UpperTheory.Kun.genK (Gq q) (res _ (tw q (j + 1))) (res _ (tw q j)) (res _ (tw q 1)) (hr (j + 1)).2.1 (hr j).2.1
    (twPair q j 1) κ (fun T => IsUnit (q : Γ(T, ⊤)))
    (fun {T' T} f hT => by simpa using hT.map f.appTop.hom)
    (by
      intro T hT m' n' h' y
      subst h'
      refine hmono _ _ _ ((UpperTheory.locally_surjective_multiplicativeGroupKunnethMap q T hT m' j).1 y) ?_
      rintro V g ⟨p, e⟩
      exact ⟨p.1, p.2, by rw [hκ]; exact e⟩)
    (by
      intro T hT m' n' h' a b e
      subst h'
      exact (UpperTheory.locally_surjective_multiplicativeGroupKunnethMap q T hT m' j).2 (a, b) (by rw [hκ] at e; exact e))
    E hE m (m + 1) rfl
  rw [hκ] at h
  exact h

theorem UpperTheory.bijective_cohomology_gm_product_kummer_cup :
    ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ n i : ℤ, Function.Bijective fun p : Ht q E n i × Ht q E (n - 1) (i - 1) =>
        pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
          ((cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2) (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q))).cast (by ring) (by ring) : Ht q (sch.obj (Gq q) ⨯ E) n i) := by
  intro q _ E hE n i
  have key : ∀ (m j n' i' : ℤ) (hn : m + 1 = n') (hi : j + 1 = i'), Function.Bijective fun p : Ht q E n' i' × Ht q E m j =>
      pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
        ((cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2) (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q))).cast hn hi : Ht q (sch.obj (Gq q) ⨯ E) n' i') := by
    intro m j n' i' hn hi
    subst hn hi
    exact UpperTheory.Kun.main q E hE m j
  exact key (n - 1) (i - 1) n i (by ring) (by ring)
