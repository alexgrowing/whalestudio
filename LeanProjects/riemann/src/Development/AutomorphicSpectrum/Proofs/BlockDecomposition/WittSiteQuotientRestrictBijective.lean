import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBiInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.ZariskiStratumQuotient

open GlobalTheory.CompanionTheory.DisoHm

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)

abbrev mkW (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (m : ℕ) : WittVector l k →+* Wc.Wm l k m :=
  Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})

theorem span_eq (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k) (T : (stF q ρ m 𝒱).FullSubcategory) :
    ((IdF.span (sV q ρ m 𝒱).A c).S T : Ideal T.obj.B) = (stdI (stF q ρ m 𝒱) none (mkW l k m c)).S T := by
  change _ = (⊥ : Ideal T.obj.B) ⊔ _
  rw [bot_sup_eq]
  rfl

set_option maxHeartbeats 1000000 in

def scQ (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k) :
    CH.Mor (sq (IdF.top (sV q ρ m 𝒱).A) (IdF.span (sV q ρ m 𝒱).A c))
      (sq (IdF.top (sP (stF q ρ m 𝒱)).A) (stdI (stF q ρ m 𝒱) none (mkW l k m c))) (mkW l k m) where
  G := 𝟭 _
  τ T :=
    { toFun := fun x => ⟨Ideal.Quotient.factor (span_eq q ρ m 𝒱 c T).le x.1, by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.factor (span_eq q ρ m 𝒱 c T).le x.1)
        rw [← hy]
        exact Ideal.mem_map_of_mem _ trivial⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun a x => by
        obtain ⟨x, hx⟩ := x
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  nat {T T'} φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Subtype.ext ?_
    rfl

theorem scQ_bij (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k) (j : ℕ) :
    Function.Bijective ((scQ q ρ m 𝒱 c).pull j) := by
  refine idM_bij (scQ q ρ m 𝒱 c).τ (scQ q ρ m 𝒱 c).nat (fun T => ⟨?_, ?_⟩) j
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have e : Ideal.Quotient.mk ((stdI (stF q ρ m 𝒱) none (mkW l k m c)).S T) (show T.obj.B from a) =
        Ideal.Quotient.mk _ (show T.obj.B from b) := congrArg Subtype.val h
    exact Subtype.ext (Ideal.Quotient.eq.2 ((span_eq q ρ m 𝒱 c T).ge (Ideal.Quotient.eq.1 e)))
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨Ideal.Quotient.mk _ a, Ideal.mem_map_of_mem _ trivial⟩, Subtype.ext rfl⟩

theorem st_le_top (m : ℕ) (𝒱 : Set X.Opens) : stF q ρ m 𝒱 ≤ stF q ρ m {⊤} :=
  fun T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩

theorem top_F (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤) (c : Wc.Wm l k m) (j : ℕ) :
    Function.Bijective ((resO (st_le_top q ρ m 𝒱) c).pull j) := by
  have hle := st_le_top q ρ m 𝒱
  have hz := (GlobalTheory.CompanionTheory.ZarCosieve.main (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
    (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inr rfl⟩) 𝒱 (stF q ρ m {⊤}) hle
    (fun T hT => ⟨hT.1, _, rfl, by rw [hU]; exact inU_top T⟩)
    (fun _ T' _ _ hT' => ⟨hT', ⊤, rfl, inU_top T'⟩) j).2.1 (some 0) none 0 c
  have t0 := sqLe_bij (b := stdI (stF q ρ m {⊤}) none c) (b' := stdI (stF q ρ m {⊤}) none c) (std0 (stF q ρ m {⊤})) (fun _ => rfl) j
  have t1 := sqLe_bij (b := stdI (stF q ρ m 𝒱) none c) (b' := stdI (stF q ρ m 𝒱) none c) (std0 (stF q ρ m 𝒱)) (fun _ => rfl) j
  refine (Function.Bijective.of_comp_iff' t1 _).1 ?_
  have e : ⇑((sqLe (a := IdF.top (sP (stF q ρ m 𝒱)).A) (b := stdI (stF q ρ m 𝒱) none c) (a' := stdI (stF q ρ m 𝒱) (some 0) 0) (b' := stdI (stF q ρ m 𝒱) none c) (fun T => (std0 (stF q ρ m 𝒱) T).le) (fun _ => le_rfl)).pull j) ∘
      ⇑((resO hle c).pull j) = ⇑(((incl hle).sq (incl_std hle (some 0) 0) (incl_std hle none c)).pull j) ∘
      ⇑((sqLe (a := IdF.top (sP (stF q ρ m {⊤})).A) (b := stdI (stF q ρ m {⊤}) none c) (a' := stdI (stF q ρ m {⊤}) (some 0) 0) (b' := stdI (stF q ρ m {⊤}) none c) (fun T => (std0 (stF q ρ m {⊤}) T).le) (fun _ => le_rfl)).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id (Wc.Wm l k m)) (resO hle c) (sqLe (a := IdF.top (sP (stF q ρ m 𝒱)).A) (b := stdI (stF q ρ m 𝒱) none c) (a' := stdI (stF q ρ m 𝒱) (some 0) 0) (b' := stdI (stF q ρ m 𝒱) none c) (fun T => (std0 (stF q ρ m 𝒱) T).le) (fun _ => le_rfl)) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id (Wc.Wm l k m)) (sqLe (a := IdF.top (sP (stF q ρ m {⊤})).A) (b := stdI (stF q ρ m {⊤}) none c) (a' := stdI (stF q ρ m {⊤}) (some 0) 0) (b' := stdI (stF q ρ m {⊤}) none c) (fun T => (std0 (stF q ρ m {⊤}) T).le) (fun _ => le_rfl)) ((incl hle).sq (incl_std hle (some 0) 0) (incl_std hle none c)) j x).1))
    refine CrystallineSemistableComparison.P.prism (σ := RingHom.id (Wc.Wm l k m)) _ _ (𝟙 _) (fun T y => ?_) j x
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  rw [e]
  exact hz.comp t0

abbrev backF (m : ℕ) : (fl l (B.schFn q) ρ m).FullSubcategory ⥤ (stF q ρ m {⊤}).FullSubcategory :=
  (stF q ρ m {⊤}).lift (fl l (B.schFn q) ρ m).ι fun T => ⟨T.property, ⊤, rfl, inU_top T.obj⟩

def adjF (m : ℕ) : ιS q ρ m {⊤} ⊣ backF q ρ m :=
  (CategoryTheory.Equivalence.mk (ιS q ρ m {⊤}) (backF q ρ m)
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))).toAdjunction

theorem top_res (m : ℕ) (c : WittVector l k) (j : ℕ) : Function.Bijective ((resVq q ρ m {⊤} c).pull j) :=
  CrystallineSemistableComparison.P.adj (sq (IdF.top (sW l (B.schFn q) ρ m).A) (IdF.span (sW l (B.schFn q) ρ m).A c)) (ιS q ρ m {⊤}) (backF q ρ m) (adjF q ρ m) j

end Main

set_option maxHeartbeats 1000000 in

theorem main : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resVq q ρ m 𝒱 c).pull j) := by
  intro l _ k _ _ _ O _ X q ρ m 𝒱 c hU j
  have hle := st_le_top q ρ m 𝒱
  refine (Function.Bijective.of_comp_iff' (scQ_bij q ρ m 𝒱 c j) _).1 ?_
  have e : ⇑((scQ q ρ m 𝒱 c).pull j) ∘ ⇑((resVq q ρ m 𝒱 c).pull j) =
      ⇑((resO hle (mkW l k m c)).pull j) ∘ ⇑((scQ q ρ m {⊤} c).pull j) ∘ ⇑((resVq q ρ m {⊤} c).pull j) := by
    funext x
    have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := mkW l k m) (resVq q ρ m {⊤} c) (scQ q ρ m {⊤} c) j x).1
    have h2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := mkW l k m) (CH.Mor.comp (σ'' := mkW l k m) (resVq q ρ m {⊤} c) (scQ q ρ m {⊤} c))
      (resO hle (mkW l k m c)) j x).1
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := mkW l k m) (resVq q ρ m 𝒱 c) (scQ q ρ m 𝒱 c) j x).1).symm.trans
      (Eq.trans ?_ (h2.trans (congrArg _ h1)))
    refine CrystallineSemistableComparison.P.prism (σ := mkW l k m) (CH.Mor.comp (σ'' := mkW l k m) (resVq q ρ m 𝒱 c) (scQ q ρ m 𝒱 c))
      (CH.Mor.comp (σ'' := mkW l k m) (CH.Mor.comp (σ'' := mkW l k m) (resVq q ρ m {⊤} c) (scQ q ρ m {⊤} c))
        (resO hle (mkW l k m c))) (𝟙 _) (fun T y => ?_) j x
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    first
      | rfl
      | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)
  rw [e]
  exact (top_F q ρ m 𝒱 hU _ j).comp ((scQ_bij q ρ m {⊤} c j).comp (top_res q ρ m c j))

end GlobalTheory.CompanionTheory.ZariskiStratumQuotient
