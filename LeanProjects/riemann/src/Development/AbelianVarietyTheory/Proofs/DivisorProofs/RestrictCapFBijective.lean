import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

instance instSupNE (I : Type) : SemilatticeSup {S : Set I // S.Nonempty} :=
  Subtype.semilatticeSup fun _ _ h _ => h.mono Set.subset_union_left

abbrev NE (I : Type) : Type := {S : Set I // S.Nonempty}ᵒᵈ

variable {I : Type} {X : Scheme.{0}}

def NE.set (S : NE I) : Set I := (OrderDual.ofDual S).1

theorem NE.le_iff {S T : NE I} : S ≤ T ↔ T.set ⊆ S.set := Iff.rfl

theorem NE.set_inf (S T : NE I) : (S ⊓ T).set = S.set ∪ T.set := rfl

theorem NE.nonempty (S : NE I) : S.set.Nonempty := (OrderDual.ofDual S).2

def NE.single (i : I) : NE I := OrderDual.toDual ⟨{i}, Set.singleton_nonempty i⟩

def NE.pair (i j : I) : NE I := OrderDual.toDual ⟨{i, j}, Set.insert_nonempty i {j}⟩

theorem NE.set_single (i : I) : (NE.single i).set = {i} := rfl

theorem NE.set_pair (i j : I) : (NE.pair i j).set = {i, j} := rfl

theorem NE.pair_le_single_left (i j : I) : NE.pair i j ≤ NE.single i :=
  NE.le_iff.2 (Set.singleton_subset_iff.2 (Set.mem_insert i {j}))

theorem NE.pair_le_single_right (i j : I) : NE.pair i j ≤ NE.single j :=
  NE.le_iff.2 (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem i rfl))

def NE.pt (S : NE I) : I := S.nonempty.some

theorem NE.pt_mem (S : NE I) : S.pt ∈ S.set := S.nonempty.some_mem

def cap (U : I → X.Opens) (S : NE I) : X.Opens := ⨅ i ∈ S.set, U i

theorem cap_le (U : I → X.Opens) {S : NE I} {i : I} (h : i ∈ S.set) : cap U S ≤ U i := iInf₂_le i h

theorem cap_mono (U : I → X.Opens) : Monotone (cap U) := fun _ _ h => le_iInf₂ fun i hi => iInf₂_le i (h hi)

theorem cap_inf (U : I → X.Opens) (S T : NE I) : cap U (S ⊓ T) = cap U S ⊓ cap U T := by
  simp only [cap, NE.set_inf, iInf_union]

theorem cap_single (U : I → X.Opens) (i : I) : cap U (NE.single i) = U i := by
  simp [cap, NE.set_single]

theorem cap_pair (U : I → X.Opens) (i j : I) : cap U (NE.pair i j) = U i ⊓ U j := by
  rw [cap, NE.set_pair, iInf_insert, iInf_singleton]

theorem cap_iSup (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) : ⨆ S, cap U S = ⊤ :=
  eq_top_iff.2 (hU ▸ iSup_le fun i => (cap_single U i).symm.le.trans (le_iSup (cap U) (NE.single i)))

theorem isAffineOpen_cap [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) (S : NE I) :
    IsAffineOpen (cap U S) := by
  have key : ∀ s : Set I, s.Finite → s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) := by
    intro s hs
    obtain ⟨t, rfl⟩ := hs.exists_finset_coe
    classical
    induction t using Finset.induction_on with
    | empty => intro h; simp at h
    | insert a t _ ih =>
      intro _
      rw [Finset.coe_insert]
      rcases (t : Set I).eq_empty_or_nonempty with ht | ht
      · rw [ht, iInf_insert, iInf_emptyset, inf_top_eq]; exact hU a
      · rw [iInf_insert]; exact hinf _ _ (hU a) (ih (Set.toFinite _) ht)
  exact key _ (Set.toFinite _) S.nonempty

def capAff [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) (S : NE I) : X.affineOpens :=
  ⟨cap U S, isAffineOpen_cap U hU hinf S⟩

theorem capAff_mono [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) :
    Monotone (capAff U hU hinf) := fun _ _ h => cap_mono U h

section Maps

variable {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

abbrev capF : (NE I)ᵒᵖ ⥤ CommAlgCat.{0} R := (capAff_mono U hU hinf).functor.op ⋙ OAff s

def cv (T : (NE I)ᵒᵖ) : (capF s U hU hinf).obj T ≃+* Γ(X, cap U T.unop) := RingEquiv.refl _

theorem cv_mp {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') (b : (capF s U hU hinf).obj T) :
    cv s U hU hinf T' (mp (capF s U hU hinf) a b) = rsT (cv s U hU hinf T b) (cap U T'.unop) :=
  (GlobalTheory.KS.rsT_of_le (O₀ := cap U T.unop) (cap_mono U (leOfHom a.unop)) b).symm

theorem cv_smul {T : (NE I)ᵒᵖ} (r : R) (b : (capF s U hU hinf).obj T) :
    cv s U hU hinf T (r • b) = constFn s (cap U T.unop) r * cv s U hU hinf T b :=
  Algebra.smul_def r b

def toPos (c : C1 U) : CatCoh.C1 (capF s U hU hinf) :=
  fun T T' _ => (cv s U hU hinf T').symm (rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop))

def toCech (f : CatCoh.C1 (capF s U hU hinf)) : C1 U := fun i j =>
  rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single i)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_left i j)).op))
      (U i ⊓ U j) -
    rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single j)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_right i j)).op))
      (U i ⊓ U j)

theorem cv_toPos (c : C1 U) {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') :
    cv s U hU hinf T' (toPos s U hU hinf c T T' a) = rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop) :=
  RingEquiv.apply_symm_apply _ _

theorem toCech_apply (f : CatCoh.C1 (capF s U hU hinf)) (i j : I) :
    toCech s U hU hinf f i j =
      rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single i)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_left i j)).op))
        (U i ⊓ U j) -
      rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single j)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_right i j)).op))
        (U i ⊓ U j) := rfl

theorem restrict_capF_bijective (hcov : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (OAff s) (capAff_mono U hU hinf).functor.op).pull1 :=
  GlobalTheory.CoverO.restrict_bijective R X s (NE I) (capAff U hU hinf) (capAff_mono U hU hinf)
    (fun S T => cap_inf U S T) (cap_iSup U hcov)

end Maps

end GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

variable {I : Type} {X : Scheme.{0}} {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

theorem NE.pt_single (i : I) : (NE.single i).pt = i := Set.mem_singleton_iff.1 (NE.pt_mem (NE.single i))

theorem toPos_lc {n : ℕ} (cc : Fin n → R) (b : Fin n → C1 U) :
    toPos s U hU hinf (fun i j => ∑ a, constFn s (U i ⊓ U j) (cc a) * b a i j) =
      ∑ a, cc a • toPos s U hU hinf (b a) := by
  funext T T' φ
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt :=
    le_inf (cap_le U ((NE.le_iff.1 (leOfHom φ.unop)) T.unop.pt_mem)) (cap_le U T'.unop.pt_mem)
  apply (cv s U hU hinf T').injective
  simp only [cv_toPos, Finset.sum_apply, Pi.smul_apply, map_sum, cv_smul, GlobalTheory.KS.rsT_sum, GlobalTheory.KS.rsT_mul,
    GlobalTheory.KS.rsT_constFn s hle]

theorem toCech_sub (f f' : CatCoh.C1 (capF s U hU hinf)) :
    toCech s U hU hinf (f - f') = toCech s U hU hinf f - toCech s U hU hinf f' := by
  funext i j
  simp only [toCech_apply, Pi.sub_apply, map_sub, GlobalTheory.KS.rsT_sub]
  abel

theorem toCech_lc {n : ℕ} (cc : Fin n → R) (f : Fin n → CatCoh.C1 (capF s U hU hinf)) :
    toCech s U hU hinf (∑ a, cc a • f a) =
      fun i j => ∑ a, constFn s (U i ⊓ U j) (cc a) * toCech s U hU hinf (f a) i j := by
  funext i j
  have hle : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  simp only [toCech_apply, Finset.sum_apply, Pi.smul_apply, map_sum, cv_smul, GlobalTheory.KS.rsT_sum, GlobalTheory.KS.rsT_mul,
    GlobalTheory.KS.rsT_constFn s hle, mul_sub, Finset.sum_sub_distrib]
  refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => ?_) (Finset.sum_congr rfl fun a _ => ?_) <;>
    rw [cv_smul, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_constFn s hle]

end GlobalTheory.CechCmp
