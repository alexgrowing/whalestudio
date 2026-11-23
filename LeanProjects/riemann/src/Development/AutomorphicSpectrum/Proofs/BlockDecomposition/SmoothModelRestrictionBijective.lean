import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocVan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG GlobalTheory.CompanionTheory.DisoHm

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatRes

section T
variable {R : Type} [CommRing R]

universe u v

theorem tens_of_bij {M : Type u} {M' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Bijective f) (g : R → M → M') (hg : ∀ n x, g n x = n • f x) :
    Tens R (N := fun _ : Unit => R) (M := fun _ => M) (M' := M') (fun _ n x => g n x) := by
  let e : (∀ _ : Unit, R ⊗[R] M) ≃+ M :=
    (AddEquiv.piUnique (fun _ : Unit => R ⊗[R] M)).trans (TensorProduct.lid R M).toAddEquiv
  have he : ∀ n x, e (Pi.single () (n ⊗ₜ x)) = n • x := fun n x => by simp [e]
  refine ⟨e.trans (AddEquiv.ofBijective f.toAddMonoidHom hf), fun _ n x => ?_⟩
  change f (e _) = _
  rw [he, map_smul]
  exact (hg n x).symm

theorem bij_of_tens {M : Type u} {M' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup M']
    (g : R → M → M') (h : Tens R (N := fun _ : Unit => R) (M := fun _ => M) (M' := M') (fun _ n x => g n x)) :
    Function.Bijective (g 1) := by
  obtain ⟨G, hG⟩ := h
  let e : (∀ _ : Unit, R ⊗[R] M) ≃+ M :=
    (AddEquiv.piUnique (fun _ : Unit => R ⊗[R] M)).trans (TensorProduct.lid R M).toAddEquiv
  have he : ∀ n x, e (Pi.single () (n ⊗ₜ x)) = n • x := fun n x => by simp [e]
  have h3 : ∀ x, e.symm x = Pi.single () ((1 : R) ⊗ₜ x) := fun x => by
    refine (AddEquiv.symm_apply_eq e).2 ?_
    rw [he, one_smul]
  have e2 : g 1 = e.symm.trans G := funext fun x => by
    change _ = G (e.symm x)
    rw [h3, hG]
  rw [e2]
  exact (e.symm.trans G).bijective
end T

section Loc
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}

theorem crit_top {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) (r : ℤ) :
    Q.Crit (fun _ => IdF.top Φ.A) r := fun _ _ => ⟨fun _ _ => trivial, fun _ => trivial⟩

theorem topBot_bij {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (T : C) :
    Function.Bijective ((toSq (IdF.top A) (IdF.bot A) (fun _ => rfl)).τ T) := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have e : Ideal.Quotient.mk ((IdF.bot A).S T) (show A.obj T from x) = Ideal.Quotient.mk _ (show A.obj T from y) :=
      congrArg Subtype.val hxy
    exact sub_eq_zero.1 (Ideal.Quotient.eq.1 e)
  · obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨z, rfl⟩

theorem local_bij (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) (hn : IsNilpotent (p : R)) (q : X ⟶ Spec (CommRingCat.of O))
    (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ} (c : Coord q V d)
    (h : St (γ := γ) (p := p) (q := q) (κ := κ) FlatT {V} ≤ St ⊤ {V}) (j : ℕ) :
    Function.Bijective ((incl h).o.pull j) := by
  obtain ⟨c', hF, -⟩ := GlobalTheory.CompanionTheory.FlatChartP.exists_flat_chart γ p hp hn q κ c
  have hg := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hQa : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} T → InU V T := by
    rintro T ⟨-, W, rfl, hW⟩
    exact hW
  have hQf : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) FlatT {V} T → InU V T := by
    rintro T ⟨-, W, rfl, hW⟩
    exact hW
  have hDa : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} c'.D := ⟨trivial, V, rfl, c'.inV⟩
  have hDf : St (γ := γ) (p := p) (q := q) (κ := κ) FlatT {V} c'.D := ⟨hF, V, rfl, c'.inV⟩
  obtain ⟨PA, hPA⟩ := poly_all γ p hp q κ ⊤ (Or.inl rfl) {V}
  obtain ⟨PF, hPF⟩ := poly_all γ p hp q κ FlatT (Or.inr rfl) {V}
  let E := c'.frame hg _ hQa hDa
  let E' := c'.frame hg _ hQf hDf
  let e : E.D ⟶ (incl h).G.obj E'.D := ObjectProperty.homMk (𝟙 c'.D)
  have he : (incl h).Fr E E' e := by
    intro i T s s'
    rfl
  have key := loc_bc (R := R) (R' := R) (m := incl h) PA PF E E' e he (fun _ => Function.injective_id) (ι := Unit) (fun _ => R)
    (fun _ => LinearMap.id) (fun _ _ => IdF.top _) (fun _ _ => IdF.bot _) (fun _ => IdF.top _) (fun _ => IdF.bot _) 0
    (fun _ => ⟨fun _ _ _ _ => trivial, fun r _ => crit_top PA r, fun r _ => (hPA r).2.1⟩)
    ⟨fun _ _ _ _ => trivial, fun r _ => crit_top PF r, fun r _ => (hPF r).2.1⟩
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ x hx => by
      have h0 : x = 0 := hx
      rw [h0, map_zero, mul_zero]
      exact Ideal.zero_mem _)
    (fun r' _ _ => by
      refine tens_of_bij (R := R) LinearMap.id Function.bijective_id _ (fun n x => ?_)
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl) j
  have b1 := bij_of_tens _ key
  let Ma := toSq (IdF.top (sP (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V})).A) (IdF.bot _) (fun _ => rfl)
  let Mf := toSq (IdF.top (sP (St (γ := γ) (p := p) (q := q) (κ := κ) FlatT {V})).A) (IdF.bot _) (fun _ => rfl)
  have ta : Function.Bijective (Ma.pull j) := idM_bij Ma.τ Ma.nat (fun T => topBot_bij _) j
  have tf : Function.Bijective (Mf.pull j) := idM_bij Mf.τ Mf.nat (fun T => topBot_bij _) j
  refine (Function.Bijective.of_comp_iff' tf _).1 ?_
  have b2 := b1.comp ta
  convert b2 using 1
  funext x
  let sc := (incl h).sqC (1 : R) (a := IdF.top _) (b := IdF.bot _) (a' := IdF.top _) (b' := IdF.bot _) (fun _ _ _ => trivial) (fun T x hx => by
      have h0 : x = 0 := hx
      rw [h0, map_zero, mul_zero]
      exact Ideal.zero_mem _)
  refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (incl h).o Mf j x).1).symm.trans
    (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) Ma sc j x).1))
  refine CrystallineSemistableComparison.P.prism (σ := RingHom.id R) (CH.Mor.comp (σ'' := RingHom.id R) (incl h).o Mf)
    (CH.Mor.comp (σ'' := RingHom.id R) Ma sc) (𝟙 _) (fun T y => ?_) j x
  refine Subtype.ext ?_
  exact congrArg (Ideal.Quotient.mk _) (by
    rw [map_one]
    exact one_mul _)

end Loc

section Glue
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {γ : DividedPowers I} {p : ℕ} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem st_le (𝒱 : Set X.Opens) : St (γ := γ) (p := p) (q := q) (κ := κ) FlatT 𝒱 ≤ St ⊤ 𝒱 :=
  fun _ hT => ⟨trivial, hT.2⟩

set_option maxHeartbeats 1000000 in

theorem glue (hp : p ≠ 0) (hn : IsNilpotent (p : R)) (U : Cov q) (j : ℕ) :
    Function.Bijective ((incl (st_le (γ := γ) (p := p) (q := q) (κ := κ) (Set.range U.U))).o.pull j) := by
  refine cover_bij (incl (st_le (γ := γ) (p := p) (q := q) (κ := κ) (Set.range U.U))).o
    (fun α T => InU (U.U α) T.obj) (fun α T => InU (U.U α) T.obj) (fun α T T' φ hT => Site.inU_hom φ.hom hT)
    (fun α T T' φ hT => Site.inU_hom φ.hom hT) (fun T => ?_) (fun T => ?_) (fun α T hT => hT)
    (fun S hS j => ?_) j
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  · obtain ⟨-, V, ⟨α, rfl⟩, hV⟩ := T.property
    exact ⟨α, hV⟩
  have h₁L : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {⨅ α ∈ S, U.U α} T →
      ∃ hp : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U) T,
        capS (fun α (T : (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have h₁O : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) FlatT {⨅ α ∈ S, U.U α} T →
      ∃ hp : St (γ := γ) (p := p) (q := q) (κ := κ) FlatT (Set.range U.U) T,
        capS (fun α (T : (St (γ := γ) (p := p) (q := q) (κ := κ) FlatT (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S ⟨T, hp⟩ :=
    fun T hT => ⟨((st_inf _ U S hS T).1 hT).1, ((st_inf _ U S hS T).1 hT).2⟩
  have aL := nestAdj h₁L (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  have aO := nestAdj h₁O (fun T => (st_inf _ U S hS T.obj.obj).2 ⟨T.obj.property, T.property⟩)
  let rL : CH.Mor ((capS (fun α (T : (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      CH.modF (sP (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U))).A)
      (CH.modF (sP (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {⨅ α ∈ S, U.U α})).A) (RingHom.id R) :=
    CH.Mor.restrict _ (nestF h₁L)
  let rO : CH.Mor ((capS (fun α (T : (St (γ := γ) (p := p) (q := q) (κ := κ) FlatT (Set.range U.U)).FullSubcategory) => InU (U.U α) T.obj) S).ι ⋙
      CH.modF (sP (St (γ := γ) (p := p) (q := q) (κ := κ) FlatT (Set.range U.U))).A)
      (CH.modF (sP (St (γ := γ) (p := p) (q := q) (κ := κ) FlatT {⨅ α ∈ S, U.U α})).A) (RingHom.id R) :=
    CH.Mor.restrict _ (nestF h₁O)
  have bL : Function.Bijective (rL.pull j) := CrystallineSemistableComparison.P.adj _ _ _ aL j
  have bO : Function.Bijective (rO.pull j) := CrystallineSemistableComparison.P.adj _ _ _ aO j
  obtain ⟨α, hα⟩ := id hS
  obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S, U.U α) ≤ U.U α) (U.inter S ⟨α, hα⟩)
  have hloc := local_bij γ p hp hn q κ c' (st_le _) j
  refine (Function.Bijective.of_comp_iff' bO _).1 ?_
  have e : ∀ x, rO.pull j ((morU (incl (st_le (γ := γ) (p := p) (q := q) (κ := κ) (Set.range U.U))).o
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hT α hα).pull j x) =
      (incl (st_le (γ := γ) (p := p) (q := q) (κ := κ) {⨅ α ∈ S, U.U α})).o.pull j (rL.pull j x) := by
    intro x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) _ rO j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) rL _ j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id R) _ _ (𝟙 _) (fun T y => ?_) j x
    rfl
  have e2 := funext e
  refine (show Function.Bijective (fun x => rO.pull j ((morU (incl (st_le (γ := γ) (p := p) (q := q) (κ := κ) (Set.range U.U))).o
      (U := capS (fun α T => InU (U.U α) T.obj) S) (U' := capS (fun α T => InU (U.U α) T.obj) S)
      fun T hT α hα => hT α hα).pull j x)) from ?_)
  rw [e2]
  exact hloc.comp bL

end Glue

section Top
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {γ : DividedPowers I} {p : ℕ} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem st_top_eq (Q : ObjectProperty (Thick (nlFun γ p X q κ))) : St Q {⊤} = Q := by
  funext T
  exact propext ⟨fun h => h.1, fun h => ⟨h, ⊤, rfl, inU_top T⟩⟩

theorem all_flat (hp : p ≠ 0) (hn : IsNilpotent (p : R)) (U : Cov q) (j : ℕ) :
    Function.Bijective ((incl (st_le (γ := γ) (p := p) (q := q) (κ := κ) {⊤})).o.pull j) := by
  have hUs : sSup (Set.range U.U) = ⊤ := by
    rw [sSup_range]
    exact U.cover
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup (Set.range U.U) := fun W _ => by
    rw [hUs]
    exact le_top
  have hfa : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩
  have hff : St (γ := γ) (p := p) (q := q) (κ := κ) FlatT (Set.range U.U) ≤ St FlatT {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩
  have za := (zar (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) (Set.range U.U) {⊤} hfa hc j).2.2
  have zf := (zar (γ := γ) (p := p) (q := q) (κ := κ) FlatT (Or.inr ⟨hp, Or.inr rfl⟩) (Set.range U.U) {⊤} hff hc j).2.2
  have g := glue (γ := γ) (κ := κ) hp hn U j
  refine (Function.Bijective.of_comp_iff' zf _).1 ?_
  have e : ⇑((incl hff).o.pull j) ∘ ⇑((incl (st_le (γ := γ) (p := p) (q := q) (κ := κ) {⊤})).o.pull j) =
      ⇑((incl (st_le (γ := γ) (p := p) (q := q) (κ := κ) (Set.range U.U))).o.pull j) ∘ ⇑((incl hfa).o.pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact g.comp za

end Top

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}

def scM (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ)
    (Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) :
    CH.Mor (Q.ι ⋙ Wc.OM l (B.schFn q) ρ m) (CH.modF (sP Q).A) (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})) where
  G := 𝟭 _
  τ T := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem scM_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ)
    (Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (j : ℕ) : Function.Bijective ((scM q ρ m Q).pull j) :=
  idM_bij (scM q ρ m Q).τ (scM q ρ m Q).nat (fun _ => Function.bijective_id) j

theorem nil_l (k : Type) [Field k] [CharP k l] [PerfectRing k l] (m : ℕ) : IsNilpotent ((l : ℕ) : Wc.Wm l k m) := ⟨m, by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _⟩

set_option maxHeartbeats 1600000 in

theorem resF_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (m j : ℕ) :
    Function.Bijective (resF l (B.schFn q) ρ m j) := by
  have hp : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have ho := all_flat (γ := Wc.pd l k m) (κ := (Wc.res l k m).comp ρ) hp (nil_l k m) U j
  have key : Function.Bijective ((CH.Mor.restrict (Wc.OM l (B.schFn q) ρ m)
      (St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT {⊤}).ι).pull j) := by
    have r1 : Function.Bijective ((CH.Mor.restrict (Wc.OM l (B.schFn q) ρ m)
        (St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) ⊤ {⊤}).ι).pull j) :=
      CrystallineSemistableComparison.P.mapH_bij _ (GlobalTheory.CompanionTheory.CosieveBC.restrict_bij _ (fun T => ⟨trivial, ⊤, rfl, inU_top T⟩)) j
    have c1 := scM_bij q ρ m (St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) ⊤ {⊤}) j
    have c2 := scM_bij q ρ m (St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT {⊤}) j
    refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
    have e : ⇑((scM q ρ m (St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT {⊤})).pull j) ∘
        ⇑((CH.Mor.restrict (Wc.OM l (B.schFn q) ρ m)
          (St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT {⊤}).ι).pull j) =
        ⇑((incl (st_le (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) {⊤})).o.pull j) ∘
        ⇑((scM q ρ m (St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) ⊤ {⊤})).pull j) ∘
        ⇑((CH.Mor.restrict (Wc.OM l (B.schFn q) ρ m)
          (St (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) ⊤ {⊤}).ι).pull j) := by
      funext x
      obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
      rfl
    rw [e]
    exact ho.comp (c1.comp r1)
  have e2 := st_top_eq (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
  exact (congrArg (fun Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m)) =>
    Function.Bijective ((CH.Mor.restrict (Wc.OM l (B.schFn q) ρ m) Q.ι).pull j)) e2).mp key

end Main

theorem flat_restriction : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K),
    M.Sm → ∀ m j, Function.Bijective (resF l (B.schFn M.p) r.ρ m j) := by
  intro l _ K r M hM m j
  haveI : IsProper M.p := GlobalTheory.CommonModel.isProper_of_isProjOver hM.1.1
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  exact resF_bij M.p r.ρ U m j

end GlobalTheory.CompanionTheory.FlatRes
