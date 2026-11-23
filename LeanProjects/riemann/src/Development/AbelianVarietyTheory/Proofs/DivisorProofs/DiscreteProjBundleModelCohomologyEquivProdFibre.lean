import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleCochainPresheafIsSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueCochainOnDiscProduct
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

noncomputable section

namespace GlobalTheory.EtC.DiscCoch

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := GlobalTheory.T.projBundleCochainPresheaf_isSheaf R q N I n

theorem jsec_bij (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) (U : Scheme.{0}) :
    Function.Bijective (fun c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n =>
      (Jsec c : Sec ((Jcx R q N I).X n) U)) := by
  have := isIso_toSheafify Scheme.etaleTopology.{0} (cotPre_isSheaf R q N I n)
  have h2 : IsIso ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)) := inferInstance
  exact ConcreteCategory.bijective_of_isIso ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U))

theorem glue (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ)
    (c : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n)
    (hc : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c V (F.map g.op x) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c U x) (zero_add n)) :
    ∃! γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (U : Scheme.{0}) (x : F.obj (op U)),
      (Cochain.ofHom ((chains R).map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))))).comp γ (zero_add n) =
        c U x := GlobalTheory.T.unique_cochain_on_disc_product R q N I F n c hc

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {F : PSh}

theorem sec_map_at_zero {A B : Shv R} {U : Scheme.{0}} (φ : A ⟶ B) : Sec.map φ (0 : Sec A U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

theorem jsec_res {n : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec.res g (Jsec c) = Jsec ((Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp c (zero_add n)) :=
  (ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).naturality g.op) c).symm

theorem jsec_d {n m : ℤ} (hm : n + 1 = m) {U : Scheme.{0}} (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec.map ((Jcx R q N I).d n m) (Jsec c) = Jsec (δ n m c) := by
  subst hm
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} (cotD R q N I n))) c
  have hd : (Jcx R q N I).d n (n + 1) = (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N I n) :=
    by simp only [Jcx, CochainComplex.of_d]
  rw [hd]
  exact h.symm

theorem jsec_add {n : ℤ} {U : Scheme.{0}} (a b : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    (Jsec (a + b) : Sec ((Jcx R q N I).X n) U) = Jsec a + Jsec b :=
  map_add ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom a b

theorem jsec_zero {n : ℤ} {U : Scheme.{0}} :
    (Jsec (0 : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) : Sec ((Jcx R q N I).X n) U) = 0 :=
  map_zero ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom

def ptFst {U : Scheme.{0}} (x : F.obj (op U)) : sch.obj U ⟶ disc.obj F := disc.map (yonedaEquiv.symm x)

theorem ptFst_res {V U : Scheme.{0}} (g : V ⟶ U) (x : F.obj (op U)) : ptFst (F.map g.op x) = sch.map g ≫ ptFst x := by
  have e : yonedaEquiv.symm (F.map g.op x) = yoneda.map g ≫ yonedaEquiv.symm x := yonedaEquiv_symm_map g.op x
  show disc.map (yonedaEquiv.symm (F.map g.op x)) = disc.map (yoneda.map g) ≫ disc.map (yonedaEquiv.symm x)
  exact (congrArg disc.map e).trans (disc.map_comp _ _)

def ptMap {U : Scheme.{0}} (x : F.obj (op U)) : sch.obj U ⨯ fibQ q N ⟶ disc.obj F ⨯ fibQ q N :=
  prod.map (ptFst x) (𝟙 (fibQ q N))

def ptPull {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {U : Scheme.{0}} (x : F.obj (op U)) :
    Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n :=
  (Cochain.ofHom ((chains R).map (ptMap (q := q) (N := N) x))).comp γ (zero_add n)

theorem ptMap_res {V U : Scheme.{0}} (g : V ⟶ U) (x : F.obj (op U)) :
    (ptMap (F.map g.op x) : sch.obj V ⨯ fibQ q N ⟶ _) = prod.map (sch.map g) (𝟙 (fibQ q N)) ≫ ptMap x := by
  unfold ptMap
  rw [ptFst_res, prod.map_map, Category.comp_id]

theorem ptPull_res {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : F.obj (op U)) : ptPull γ (F.map g.op x) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (ptPull γ x) (zero_add n) := by
  unfold ptPull
  rw [ptMap_res (q := q) (N := N), Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem comp_δ {K L M : Cx R} {n m : ℤ} (hm : n + 1 = m) (f : K ⟶ L) (γ : Cochain L M n) :
    δ n m ((Cochain.ofHom f).comp γ (zero_add n)) = (Cochain.ofHom f).comp (δ n m γ) (zero_add m) := by
  rw [δ_zero_cochain_comp _ _ _ hm, δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

theorem ptPull_δ {n m : ℤ} (hm : n + 1 = m) (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n)
    {U : Scheme.{0}} (x : F.obj (op U)) : ptPull (δ n m γ) x = δ n m (ptPull γ x) :=
  (comp_δ hm _ γ).symm

theorem ptPull_add {n : ℤ} (a b : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {U : Scheme.{0}}
    (x : F.obj (op U)) : ptPull (a + b) x = ptPull a x + ptPull b x := Cochain.comp_add _ _ _ _

theorem ptPull_zero {n : ℤ} {U : Scheme.{0}} (x : F.obj (op U)) :
    ptPull (0 : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) x = 0 := Cochain.comp_zero _ _

theorem ev_zero_of_v {E : Spc} {L : Cx R} {n : ℤ} (β : Cochain ((chains R).obj E) L n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (hβ : β.v (-(p : ℤ)) s h = 0) (U : Scheme.{0}) (x : Sx E p U) : ev β p s h U x = 0 := by
  rw [ev_def, hβ, comp_zero]
  rfl

theorem conc_δ {L : Cx R} {n m : ℤ} (hm : n + 1 = m) (β : Cochain ((chains R).obj (disc.obj F)) L n)
    (hβ : ∀ (p : ℕ) s h U x, ev β (p + 1) s h U x = 0) :
    ∀ (p : ℕ) s h U x, ev (δ n m β) (p + 1) s h U x = 0 := by
  intro p s h U x
  rw [ev_δ_succ hm β U p (s - m + n) s (by omega) h x, hβ, sec_map_at_zero, zero_add]
  cases p with
  | zero =>
    have hf : ∀ i, Sx.face x i = x := fun i => rfl
    simp [Fin.sum_univ_two, hf]
  | succ p => simp [hβ]

end GlobalTheory.EtC.DiscCoch

namespace GlobalTheory.EtC.DiscCoch

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {F : PSh}

def aS {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx (disc.obj F) p U → Sec ((Jcx R q N I).X s) U
  | 0, s, h, U, x => (show n = s by simpa using h) ▸ Jsec (ptPull γ (show F.obj (op U) from x))
  | _ + 1, _, _, _, _ => 0

theorem exS {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) :
    ∃ β : Cochain ((chains R).obj (disc.obj F)) (Jcx R q N I) n,
      (∀ (U : Scheme.{0}) (x : F.obj (op U)), ev β 0 n (by simp) U x = Jsec (ptPull γ x)) ∧
      ∀ (p : ℕ) s h U x, ev β (p + 1) s h U x = 0 := by
  obtain ⟨β, hβ⟩ := ev_exists (E := disc.obj F) (I := Jcx R q N I) (n := n) (aS γ) (by
    intro p s h V U g x
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      exact (jsec_res g _).trans (congrArg Jsec (ptPull_res γ g x).symm)
    | succ p => exact map_zero _)
  exact ⟨β, fun U x => hβ 0 n _ U x, fun p s h U x => hβ (p + 1) s h U x⟩

theorem model : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ), ∃ e : CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n ≃+ CohomologyClass ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (β : Cocycle ((chains R).obj (disc.obj F)) (Jcx R q N I) n) (γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), β.1.v (-(p : ℤ)) s h = 0) → (∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ev β.1 0 n (by simp) U x = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = ev γ.1 k s hs V (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) → e (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  intro R _ q N I F n
  choose S hS0 hS1 using fun (m : ℤ) (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I m) => exS γ
  have hSδ : ∀ (m m' : ℤ) (hm : m + 1 = m') (η : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I m),
      S m' (δ m m' η) = δ m m' (S m η) := by
    intro m m' hm η
    apply ev_ext
    intro p s h U x
    cases p with
    | zero =>
      obtain rfl : m' = s := by omega
      rw [hS0, ev_δ_zero hm (S m η) U m m' (by simp) h x, hS0, jsec_d hm, ptPull_δ hm]
    | succ p => rw [hS1, conc_δ hm _ (hS1 m η)]
  have hSadd : ∀ (γ γ' : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n), S n (γ + γ') = S n γ + S n γ' := by
    intro γ γ'
    apply ev_ext
    intro p s h U x
    rw [ev_add]
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      rw [hS0, hS0, hS0, ptPull_add, jsec_add]
    | succ p => rw [hS1, hS1, hS1, add_zero]
  have hSzero : ∀ m : ℤ, S m 0 = 0 := by
    intro m
    apply ev_ext
    intro p s h U x
    rw [ev_zero]
    cases p with
    | zero =>
      obtain rfl : m = s := by omega
      rw [hS0, ptPull_zero, jsec_zero]
    | succ p => rw [hS1]
  have hScyc : ∀ γ : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, δ n (n + 1) (S n γ.1) = 0 := by
    intro γ
    rw [← hSδ n (n + 1) rfl, Cocycle.δ_eq_zero, hSzero]
  let Sc : Cocycle ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n →+
      CohomologyClass ((chains R).obj (disc.obj F)) (Jcx R q N I) n :=
    AddMonoidHom.mk' (fun γ => CohomologyClass.mk (Cocycle.mk (S n γ.1) (n + 1) rfl (hScyc γ))) (by
      intro a b
      rw [← CohomologyClass.mk_add]
      exact congrArg CohomologyClass.mk (Cocycle.ext (hSadd a.1 b.1)))
  have hcob : coboundaries ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n ≤ Sc.ker := by
    rintro ⟨γ, hγ⟩ ⟨n', hn', η, rfl⟩
    change CohomologyClass.mk _ = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', S n' η, (hSδ n' n hn' η).symm⟩
  let Φ := CohomologyClass.descAddMonoidHom Sc hcob
  have hnat : ∀ (m : ℤ) (b : Cochain ((chains R).obj (disc.obj F)) (Jcx R q N I) m)
      (c' : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I m),
      (∀ U x, Jsec (c' U x) = ev b 0 m (by simp) U x) →
      ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c' V (F.map g.op x) =
        (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c' U x) (zero_add m) := by
    intro m b c' hc' V U g x
    apply (jsec_bij R q N I m V).1
    change Jsec _ = Jsec _
    rw [hc', ← jsec_res, hc', ev_res]
    rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨γ, rfl⟩ := c.mk_surjective
    change CohomologyClass.mk _ = 0 at hc
    rw [CohomologyClass.mk_eq_zero_iff] at hc
    obtain ⟨n', hn', β', hβ'⟩ := hc
    have hc' : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n',
        Jsec c = ev β' 0 n' (by simp) U x := fun U x => (jsec_bij R q N I n' U).2 _
    choose c' hc' using hc'
    obtain ⟨η, hη, -⟩ := glue R q N I F n' c' (hnat n' β' c' hc')
    have h2 : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ptPull (δ n' n η) x = ptPull γ.1 x := by
      intro U x
      have h1 : ptPull η x = c' U x := hη U x
      rw [ptPull_δ hn', h1]
      apply (jsec_bij R q N I n U).1
      change Jsec _ = Jsec _
      rw [← jsec_d hn', hc', ← ev_δ_zero hn' β' U n' n (by simp) (by simp) x]
      change ev (δ n' n β') 0 n _ U x = _
      rw [hβ']
      exact hS0 n γ.1 U x
    have huniq := (glue R q N I F n (fun U x => ptPull γ.1 x) (fun V U g x => ptPull_res γ.1 g x)).unique
      (y₁ := γ.1) (y₂ := δ n' n η) (fun U x => rfl) h2
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', η, huniq.symm⟩
  have hΦsurj : Function.Surjective Φ := by
    intro c
    obtain ⟨α, hαc, hα0⟩ := GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos R F (Jcx R q N I) n c
    have hc' : ∀ (U : Scheme.{0}) (x : F.obj (op U)), ∃ c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
        Jsec c = ev α.1 0 n (by simp) U x := fun U x => (jsec_bij R q N I n U).2 _
    choose c' hc' using hc'
    obtain ⟨γ, hγ, -⟩ := glue R q N I F n c' (hnat n α.1 c' hc')
    have hδ : δ n (n + 1) γ = 0 := by
      refine (glue R q N I F (n + 1) (fun U x => 0) (fun V U g x => (Cochain.comp_zero _ _).symm)).unique
        (fun U x => ?_) (fun U x => Cochain.comp_zero _ _)
      show ptPull (δ n (n + 1) γ) x = 0
      rw [ptPull_δ rfl, show ptPull γ x = c' U x from hγ U x]
      apply (jsec_bij R q N I (n + 1) U).1
      change Jsec _ = Jsec _
      rw [← jsec_d rfl, hc', ← ev_δ_zero rfl α.1 U n (n + 1) (by simp) (by simp) x, Cocycle.δ_eq_zero, ev_zero,
        jsec_zero]
    refine ⟨CohomologyClass.mk (Cocycle.mk γ (n + 1) rfl hδ), ?_⟩
    rw [← hαc]
    change CohomologyClass.mk _ = _
    congr 1
    apply Cocycle.ext
    apply ev_ext
    intro p s h U x
    cases p with
    | zero =>
      obtain rfl : n = s := by omega
      show ev (S n γ) 0 n h U x = ev α.1 0 n h U x
      rw [hS0, show ptPull γ x = c' U x from hγ U x, hc']
    | succ p =>
      show ev (S n γ) (p + 1) s h U x = ev α.1 (p + 1) s h U x
      rw [hS1, ev_zero_of_v _ _ _ _ (hα0 (p + 1) (by omega) s h)]
  refine ⟨(AddEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm, fun β γ hβ0 hβc => ?_⟩
  rw [AddEquiv.symm_apply_eq]
  change CohomologyClass.mk β = CohomologyClass.mk _
  congr 1
  apply Cocycle.ext
  apply ev_ext
  intro p s h U x
  cases p with
  | zero =>
    obtain rfl : n = s := by omega
    obtain ⟨c, hc1, hc2⟩ := hβc U x
    show ev β.1 0 n h U x = ev (S n γ.1) 0 n h U x
    rw [hS0, hc1]
    congr 1
    apply ev_ext
    intro k s hs V y
    rw [hc2]
    exact (ev_pull _ γ.1 k s hs V y).symm
  | succ p =>
    show ev β.1 (p + 1) s h U x = ev (S n γ.1) (p + 1) s h U x
    rw [hS1, ev_zero_of_v _ _ _ _ (hβ0 (p + 1) (by omega) s h)]

end GlobalTheory.EtC.DiscCoch
