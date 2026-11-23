import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsomorphismPullbackCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoFlagPairSubbundleCompatStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

namespace GlobalTheory.FlagPairChain

open GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.FlagChain GlobalTheory.FlagPairExists

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def ofIso {Z : Model O} {E E' E₁ E₁' : Z.X.Modules} {φ : Z.GenIso E E'} {φ₁ : Z.GenIso E₁ E₁'}
    {N : ℕ} (P : FlagPair φ N) (e : E ≅ E₁) (e' : E' ≅ E₁')
    (h : φ.hom ≫ Z.genRes.map e'.hom = Z.genRes.map e.hom ≫ φ₁.hom) : FlagPair φ₁ N where
  fl := P.fl.ofIso e
  fl' := P.fl'.ofIso e'
  gen := P.gen
  gen_ι i := by
    change (P.gen i).hom ≫ Z.genRes.map (P.fl'.ι i ≫ e'.hom) = Z.genRes.map (P.fl.ι i ≫ e.hom) ≫ φ₁.hom
    rw [Functor.map_comp, Functor.map_comp, reassoc_of% (P.gen_ι i), h, Category.assoc]

theorem adj_symm {Z : Model O} {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {N : ℕ}
    {P Q : FlagPair φ N} (h : FlagPair.Adj P Q) : FlagPair.Adj Q P := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun i hi => ⟨(hj i hi).1.symm, (hj i hi).2.symm⟩⟩

theorem adj_of_same {Z : Model O} {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {N : ℕ}
    {P Q : FlagPair φ N} (h : ∀ i, Same (P.fl.ι i) (Q.fl.ι i) ∧ Same (P.fl'.ι i) (Q.fl'.ι i)) :
    FlagPair.Adj P Q :=
  ⟨0, fun i _ => h i⟩

theorem adj_ofIso {Z : Model O} {E E' E₁ E₁' : Z.X.Modules} {φ : Z.GenIso E E'}
    {φ₁ : Z.GenIso E₁ E₁'} {N : ℕ} {P Q : FlagPair φ N} (e : E ≅ E₁) (e' : E' ≅ E₁')
    (h : φ.hom ≫ Z.genRes.map e'.hom = Z.genRes.map e.hom ≫ φ₁.hom) (hPQ : FlagPair.Adj P Q) :
    FlagPair.Adj (ofIso P e e' h) (ofIso Q e e' h) := by
  obtain ⟨j, hj⟩ := hPQ
  exact ⟨j, fun i hi => ⟨Same.comp (hj i hi).1 e.hom, Same.comp (hj i hi).2 e'.hom⟩⟩

theorem adj_pairPull {Z Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
    {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {N : ℕ} {P Q : FlagPair φ N}
    (hPQ : FlagPair.Adj P Q) : FlagPair.Adj (pairPull hf P) (pairPull hf Q) := by
  obtain ⟨j, hj⟩ := hPQ
  exact ⟨j, fun i hi => ⟨Same.map (hj i hi).1 (Scheme.Modules.pullback f),
    Same.map (hj i hi).2 (Scheme.Modules.pullback f)⟩⟩

def pullComp {Z Z₁ Z₂ : Model O} (f : Hom Z₁ Z) (g : Hom Z₂ Z₁) {E E' : Z.X.Modules}
    {φ : Z.GenIso E E'} {N : ℕ} (P : FlagPair ((φ.pull f.comp_str).pull g.comp_str) N) :
    FlagPair (φ.pull (g.comp f).comp_str) N :=
  ofIso P ((Scheme.Modules.pullbackComp g.f f.f).app E) ((Scheme.Modules.pullbackComp g.f f.f).app E')
    (GlobalTheory.T.generic_isomorphism_pullback_comp O Z Z₁ Z₂ f g E E' φ)

abbrev Joined {Z : Model O} {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {N : ℕ}
    (P Q : FlagPair φ N) : Prop := Relation.ReflTransGen FlagPair.Adj P Q

theorem adj_pullComp_pairPull {Z Z₁ Z₂ : Model O} (f : Hom Z₁ Z) (g : Hom Z₂ Z₁)
    {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {N : ℕ} (P : FlagPair φ N) :
    FlagPair.Adj (pullComp f g (pairPull g.comp_str (pairPull f.comp_str P)))
      (pairPull (g.comp f).comp_str P) :=
  adj_of_same fun i => ⟨same_natIso (Scheme.Modules.pullbackComp g.f f.f) (P.fl.ι i),
    same_natIso (Scheme.Modules.pullbackComp g.f f.f) (P.fl'.ι i)⟩

theorem joined_pullComp {Z Z₁ Z₂ : Model O} (f : Hom Z₁ Z) (g : Hom Z₂ Z₁)
    {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {N : ℕ} {P Q : FlagPair ((φ.pull f.comp_str).pull g.comp_str) N}
    (h : Joined P Q) : Joined (pullComp f g P) (pullComp f g Q) :=
  h.lift (pullComp f g) fun _ _ hab => adj_ofIso _ _ _ hab

theorem exists_gen {Z : Model O} {E E' A A' C C' : Z.X.Modules} (φ : Z.GenIso E E')
    {a : A ⟶ E} {a' : A' ⟶ E'} {b : C ⟶ E} {b' : C' ⟶ E'} (ha : Same a b) (ha' : Same a' b')
    (ψ : Z.GenIso C C') (hψ : ψ.hom ≫ Z.genRes.map b' = Z.genRes.map b ≫ φ.hom) :
    ∃ χ : Z.GenIso A A', χ.hom ≫ Z.genRes.map a' = Z.genRes.map a ≫ φ.hom := by
  obtain ⟨e, rfl⟩ := ha
  obtain ⟨e', rfl⟩ := ha'
  refine ⟨Z.genRes.mapIso e ≪≫ ψ ≪≫ (Z.genRes.mapIso e').symm, ?_⟩
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc,
    Functor.map_comp]
  rw [← Functor.map_comp_assoc, e'.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, hψ]

theorem exists_update {Z : Model O} {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {r : ℕ}
    (P : FlagPair φ r) (j : Fin (r + 1)) {H H' : Z.X.Modules} {κ : H ⟶ E} {κ' : H' ⟶ E'}
    (ψ : Z.GenIso H H') (hψ : ψ.hom ≫ Z.genRes.map κ' = Z.genRes.map κ ≫ φ.hom)
    (hs : IsSubbundle κ) (hs' : IsSubbundle κ') (hv : IsVB H j) (hv' : IsVB H' j)
    (hl : j ≠ Fin.last r)
    (h₁ : ∀ i : Fin r, i.succ = j → Le (P.fl.ι i.castSucc) κ)
    (h₁' : ∀ i : Fin r, i.succ = j → Le (P.fl'.ι i.castSucc) κ')
    (h₂ : ∀ i : Fin r, i.castSucc = j → Le κ (P.fl.ι i.succ))
    (h₂' : ∀ i : Fin r, i.castSucc = j → Le κ' (P.fl'.ι i.succ)) :
    ∃ Q : FlagPair φ r, Same (Q.fl.ι j) κ ∧ Same (Q.fl'.ι j) κ' ∧
      ∀ i, i ≠ j → Same (Q.fl.ι i) (P.fl.ι i) ∧ Same (Q.fl'.ι i) (P.fl'.ι i) := by
  classical
  obtain ⟨g, g₁, g₂⟩ := FlagChain.exists_update P.fl j hs hv hl h₁ h₂
  obtain ⟨g', g₁', g₂'⟩ := FlagChain.exists_update P.fl' j hs' hv' hl h₁' h₂'
  have hgen : ∀ i, ∃ χ : Z.GenIso (g.F i) (g'.F i),
      χ.hom ≫ Z.genRes.map (g'.ι i) = Z.genRes.map (g.ι i) ≫ φ.hom := fun i => by
    by_cases hi : i = j
    · subst hi
      exact exists_gen φ g₁ g₁' ψ hψ
    · exact exists_gen φ (g₂ i hi) (g₂' i hi) (P.gen i) (P.gen_ι i)
  choose χ hχ using hgen
  exact ⟨⟨g, g', χ, hχ⟩, g₁, g₁', fun i hi => ⟨g₂ i hi, g₂' i hi⟩⟩

def Moves {B : Model O} {E E' : B.X.Modules} {φ : B.GenIso E E'} {r : ℕ} (P : FlagPair φ r)
    (n : Fin (r + 1)) {H H' : B.X.Modules} (κ : H ⟶ E) (κ' : H' ⟶ E') : Prop :=
  ∃ (B' : Model O) (f : Hom B' B), IsNormalScheme B'.X ∧ f.relDim = 0 ∧
    ∃ Q : FlagPair (φ.pull f.comp_str) r, Joined (pairPull f.comp_str P) Q ∧
      Same (Q.fl.ι n) ((Scheme.Modules.pullback f.f).map κ) ∧
      Same (Q.fl'.ι n) ((Scheme.Modules.pullback f.f).map κ') ∧
      ∀ i, n < i → Same (Q.fl.ι i) ((pairPull f.comp_str P).fl.ι i) ∧
        Same (Q.fl'.ι i) ((pairPull f.comp_str P).fl'.ι i)

theorem Moves.of_pull {B B₁ : Model O} {E E' : B.X.Modules} {φ : B.GenIso E E'} {r : ℕ}
    {P : FlagPair φ r} {n : Fin (r + 1)} {H H' : B.X.Modules} {κ : H ⟶ E} {κ' : H' ⟶ E'}
    (f : Hom B₁ B) (hf : f.relDim = 0)
    (h : Moves (pairPull f.comp_str P) n ((Scheme.Modules.pullback f.f).map κ)
      ((Scheme.Modules.pullback f.f).map κ')) : Moves P n κ κ' := by
  obtain ⟨B₂, g, hB₂, hg, Q, h₁, h₂, h₂', h₃⟩ := h
  refine ⟨B₂, g.comp f, hB₂, relDim_comp f g hf hg, pullComp f g Q,
    ((joined_pullComp f g h₁).head (adj_symm (adj_pullComp_pairPull f g P))), ?_, ?_, fun i hi => ⟨?_, ?_⟩⟩
  · exact (h₂.comp _).trans (same_natIso (Scheme.Modules.pullbackComp g.f f.f) κ)
  · exact (h₂'.comp _).trans (same_natIso (Scheme.Modules.pullbackComp g.f f.f) κ')
  · exact ((h₃ i hi).1.comp _).trans (same_natIso (Scheme.Modules.pullbackComp g.f f.f) (P.fl.ι i))
  · exact ((h₃ i hi).2.comp _).trans (same_natIso (Scheme.Modules.pullbackComp g.f f.f) (P.fl'.ι i))

theorem moves (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (n : ℕ) : ∀ (B : Model O), IsNormalScheme B.X → ∀ {E E' : B.X.Modules}
    {φ : B.GenIso E E'} {r : ℕ} (P : FlagPair φ r) (hn : n < r) {H H' : B.X.Modules} (κ : H ⟶ E)
    (κ' : H' ⟶ E') (ψ : B.GenIso H H'), ψ.hom ≫ B.genRes.map κ' = B.genRes.map κ ≫ φ.hom →
    IsSubbundle κ → IsSubbundle κ' → IsVB H n → IsVB H' n →
    Le κ (P.fl.ι ⟨n + 1, by omega⟩) → Le κ' (P.fl'.ι ⟨n + 1, by omega⟩) →
    Moves P ⟨n, by omega⟩ κ κ' := by
  induction n with
  | zero =>
    intro B hB E E' φ r P hn H H' κ κ' ψ _ _ _ hv hv' _ _
    have h₀ := GlobalTheory.VB.isVB_zero_iff.1 ((pairPull (Hom.id B).comp_str P).fl.isVB ⟨0, by omega⟩)
    have h₀' := GlobalTheory.VB.isVB_zero_iff.1 ((pairPull (Hom.id B).comp_str P).fl'.isVB ⟨0, by omega⟩)
    exact ⟨B, Hom.id B, hB, Nat.sub_self _, _, .refl,
      ⟨h₀.iso (GlobalTheory.VB.isVB_zero_iff.1 (hv.pullback _)), h₀.eq_of_src _ _⟩,
      ⟨h₀'.iso (GlobalTheory.VB.isVB_zero_iff.1 (hv'.pullback _)), h₀'.eq_of_src _ _⟩,
      fun _ _ => ⟨.refl _, .refl _⟩⟩
  | succ n ih =>
    intro B hB E E' φ r P hn H H' κ κ' ψ hψ hs hs' hv hv' hle hle'
    obtain ⟨B₁, f₁, K, K', μ, μ', χ, hB₁, hf₁, hμ, hμ', hK, hK', hχ, m₁, m₁', m₂, m₂'⟩ :=
      GlobalTheory.T.generic_iso_flag_pair_subbundle_compat O p B hB E E' φ r P n hn H H' κ κ' ψ hs hs' hv hv' hψ hle hle'
    refine Moves.of_pull f₁ hf₁ ?_
    obtain ⟨B₂, f₂, hB₂, hf₂, Q, k₁, k₂, k₂', k₃⟩ :=
      ih B₁ hB₁ (pairPull f₁.comp_str P) (by omega) μ μ' χ hχ hμ hμ' hK hK' m₁ m₁'
    have hn₁ : n < r + 1 := by omega
    have hn₃ : n < r := by omega
    have hc := pull_comm f₂.comp_str _ _ _ _
      (pull_comm f₁.comp_str φ ψ κ κ' hψ)
    obtain ⟨Q', l₁, l₁', l₂⟩ := exists_update Q ⟨n + 1, by omega⟩ _ hc
      (SubPull.isSubbundle_pullback _ _ f₂.f _ _ _ _ (hv.pullback f₁.f)
        (SubPull.isSubbundle_pullback _ _ f₁.f _ _ κ _ hv hs))
      (SubPull.isSubbundle_pullback _ _ f₂.f _ _ _ _ (hv'.pullback f₁.f)
        (SubPull.isSubbundle_pullback _ _ f₁.f _ _ κ' _ hv' hs'))
      ((hv.pullback _).pullback _) ((hv'.pullback _).pullback _)
      (fun e => by have := congrArg Fin.val e; simp at this; omega)
      (fun i hi => by
        obtain rfl : i = ⟨n, hn₃⟩ := Fin.ext (Nat.succ_injective (congrArg Fin.val hi))
        exact k₂.le.trans (m₂.map _))
      (fun i hi => by
        obtain rfl : i = ⟨n, hn₃⟩ := Fin.ext (Nat.succ_injective (congrArg Fin.val hi))
        exact k₂'.le.trans (m₂'.map _))
      (fun i hi => by
        obtain rfl : i = ⟨n + 1, hn⟩ := Fin.ext (congrArg Fin.val hi :)
        exact ((hle.map _).map _).trans
          (k₃ ⟨n + 2, by omega⟩ (Fin.mk_lt_mk.2 (by omega))).1.symm.le)
      (fun i hi => by
        obtain rfl : i = ⟨n + 1, hn⟩ := Fin.ext (congrArg Fin.val hi :)
        exact ((hle'.map _).map _).trans
          (k₃ ⟨n + 2, by omega⟩ (Fin.mk_lt_mk.2 (by omega))).2.symm.le)
    exact ⟨B₂, f₂, hB₂, hf₂, Q', k₁.tail ⟨⟨n + 1, by omega⟩, fun i hi =>
      ⟨(l₂ i hi).1.symm, (l₂ i hi).2.symm⟩⟩, l₁, l₁', fun i hi =>
      ⟨((l₂ i hi.ne').1).trans (k₃ i (lt_trans (Fin.mk_lt_mk.2 n.lt_succ_self) hi)).1,
       ((l₂ i hi.ne').2).trans (k₃ i (lt_trans (Fin.mk_lt_mk.2 n.lt_succ_self) hi)).2⟩⟩

theorem joined_of_same (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (n : ℕ) : ∀ (B : Model O), IsNormalScheme B.X → ∀ {E E' : B.X.Modules}
    {φ : B.GenIso E E'} {r : ℕ}, n ≤ r → ∀ P P' : FlagPair φ r,
    (∀ i : Fin (r + 1), n ≤ i → Same (P.fl.ι i) (P'.fl.ι i) ∧ Same (P.fl'.ι i) (P'.fl'.ι i)) →
    ∃ (B' : Model O) (f : Hom B' B), IsNormalScheme B'.X ∧ f.relDim = 0 ∧
      Joined (pairPull f.comp_str P) (pairPull f.comp_str P') := by
  induction n with
  | zero =>
    intro B hB E E' φ r _ P P' h
    exact ⟨B, Hom.id B, hB, Nat.sub_self _, .single (adj_pairPull _
      (adj_of_same fun i => h i (Nat.zero_le _)))⟩
  | succ n ih =>
    intro B hB E E' φ r hn P P' h
    obtain ⟨B₁, f₁, hB₁, hf₁, Q, h₁, h₂, h₂', h₃⟩ := moves p n B hB P hn (P'.fl.ι ⟨n, by omega⟩)
      (P'.fl'.ι ⟨n, by omega⟩) (P'.gen _) (P'.gen_ι _) (P'.fl.isSubbundle _) (P'.fl'.isSubbundle _)
      (P'.fl.isVB _) (P'.fl'.isVB _)
      (Le.trans ⟨P'.fl.step ⟨n, hn⟩, P'.fl.step_ι ⟨n, hn⟩⟩ (h ⟨n + 1, by omega⟩ le_rfl).1.symm.le)
      (Le.trans ⟨P'.fl'.step ⟨n, hn⟩, P'.fl'.step_ι ⟨n, hn⟩⟩ (h ⟨n + 1, by omega⟩ le_rfl).2.symm.le)
    have hn₁ : n < r + 1 := by omega
    obtain ⟨B₂, f₂, hB₂, hf₂, k₁⟩ := ih B₁ hB₁ (by omega) Q (pairPull f₁.comp_str P') fun i hi => by
      rcases hi.eq_or_lt with e | e
      · obtain rfl : i = ⟨n, hn₁⟩ := Fin.ext e.symm
        exact ⟨h₂, h₂'⟩
      · exact ⟨(h₃ i e).1.trans ((h i e).1.map _), (h₃ i e).2.trans ((h i e).2.map _)⟩
    have k₂ : Joined (pairPull f₂.comp_str (pairPull f₁.comp_str P))
        (pairPull f₂.comp_str (pairPull f₁.comp_str P')) :=
      (h₁.lift (pairPull f₂.comp_str) fun _ _ hab => adj_pairPull _ hab).trans k₁
    refine ⟨B₂, f₂.comp f₁, hB₂, relDim_comp f₁ f₂ hf₁ hf₂, ?_⟩
    exact ((joined_pullComp f₁ f₂ k₂).tail (adj_pullComp_pairPull f₁ f₂ P')).head
      (adj_symm (adj_pullComp_pairPull f₁ f₂ P))

end GlobalTheory.FlagPairChain

theorem GlobalTheory.FlagPairChain.exists_normal_modification_joined : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r), ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ Relation.ReflTransGen GlobalTheory.Vert.Model.FlagPair.Adj (GlobalTheory.FlagPairExists.pairPull f.comp_str P) (GlobalTheory.FlagPairExists.pairPull f.comp_str P') := by
  intro O _ _ _ p _ _ _ B hB E E' φ r P P'
  refine GlobalTheory.FlagPairChain.joined_of_same p r B hB le_rfl P P' fun i hi => ?_
  obtain rfl : i = Fin.last r := Fin.last_le_iff.1 hi
  exact ⟨⟨asIso (P.fl.ι _) ≪≫ (asIso (P'.fl.ι _)).symm, by simp⟩,
    ⟨asIso (P.fl'.ι _) ≪≫ (asIso (P'.fl'.ι _)).symm, by simp⟩⟩
