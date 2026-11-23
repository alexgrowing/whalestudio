import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise AddMonoidAlgebra

noncomputable section

universe u w

theorem quot_retract {R R' X Y : Type*} [Ring R] [Ring R'] [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R' Y] (P : Submodule R X) (Q : Submodule R' Y) (f : X →+ Y) (g : Y →+ X)
    (hf : ∀ x ∈ P, f x ∈ Q) (hg : ∀ y ∈ Q, g y ∈ P) (hgf : ∀ x, g (f x) = x) :
    ∃ (ι : X ⧸ P →+ Y ⧸ Q) (π : Y ⧸ Q →+ X ⧸ P), ∀ z, π (ι z) = z := by
  refine ⟨QuotientAddGroup.map P.toAddSubgroup Q.toAddSubgroup f (fun x hx => hf x hx),
    QuotientAddGroup.map Q.toAddSubgroup P.toAddSubgroup g (fun y hy => hg y hy), ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P z
  change (QuotientAddGroup.mk (g (f x)) : X ⧸ P.toAddSubgroup) = QuotientAddGroup.mk x
  rw [hgf]

section Split

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ}

theorem UT.toL_sum {η : Fin (r + 1) → Ω} {ι : Type*} (s : Finset ι) (f : ι → UT x η) :
    UT.toL (∑ j ∈ s, f j) = ∑ j ∈ s, UT.toL (f j) := rfl

theorem UT.toL_zsmul {η : Fin (r + 1) → Ω} (k : ℤ) (v : UT x η) : UT.toL (k • v) = k • UT.toL v := rfl

theorem UT.toL_add {η : Fin (r + 1) → Ω} (v v' : UT x η) : UT.toL (v + v') = UT.toL v + UT.toL v' := rfl

theorem UT.toL_zero {η : Fin (r + 1) → Ω} : UT.toL (0 : UT x η) = 0 := rfl

def upI {i : ℕ} (K : Cech.Idx (support x) i) : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i :=
  ⟨⟨K.1.1, K.1.2.1, Finset.subset_univ _⟩, K.2⟩

def downI {i : ℕ} (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (h : J.1.1 ⊆ support x) :
    Cech.Idx (support x) i :=
  ⟨⟨J.1.1, J.1.2.1, h⟩, J.2⟩

variable (η : Fin (r + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (n : ℕ) (c : ℤ)

def cf (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I →+ Ω where
  toFun w := (UT.toL (locEmb η M₀ I hI w)).coeff ((n : ℤ), c)
  map_zero' := by rw [map_zero, UT.toL_zero, AddMonoidAlgebra.coeff_zero]; rfl
  map_add' w w' := by
    rw [map_add, UT.toL_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem cf_locResS (I J : StdCell N) (hI : I.1 ⊆ support x) (hJ : J.1 ⊆ support x) (h : I.1 ⊆ J.1)
    (w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I.1) :
    cf η M₀ n c J.1 hJ (locResS I J h w) = cf η M₀ n c I.1 hI w := by
  change (UT.toL (locEmb η M₀ J.1 hJ (locRes h w))).coeff _ = (UT.toL (locEmb η M₀ I.1 hI w)).coeff _
  rw [locEmb_locRes η M₀ hI hJ h w]

theorem locEmb_locResS (I J : StdCell N) (hI : I.1 ⊆ support x) (hJ : J.1 ⊆ support x) (h : I.1 ⊆ J.1)
    (w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) I.1) :
    locEmb η M₀ J.1 hJ (locResS I J h w) = locEmb η M₀ I.1 hI w :=
  locEmb_locRes η M₀ hI hJ h w

variable {G B : SubSystem S x Ω} (hG : ∀ I, M₀.tilde 0 I = G.sub I)
  (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)

def ιfun (K : Chart x) (z : ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) K.1 :=
  (exists_locEmb_eq η M₀ ⟨K.1, K.2.1, Finset.subset_univ _⟩ K.2.2
    (twistSub_le_twLocPart η M₀ hG hB K n c z.2)).choose

theorem ιfun_mem (K : Chart x) (z : ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    ιfun η M₀ n c hG hB K z ∈ degLoc (twGraded η M₀) c ⟨K.1, K.2.1, Finset.subset_univ _⟩ :=
  (exists_locEmb_eq η M₀ ⟨K.1, K.2.1, Finset.subset_univ _⟩ K.2.2
    (twistSub_le_twLocPart η M₀ hG hB K n c z.2)).choose_spec.1

theorem ιfun_emb (K : Chart x) (z : ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    UT.toL (locEmb η M₀ K.1 K.2.2 (ιfun η M₀ n c hG hB K z)) = single ((n : ℤ), c) (z : Ω) :=
  (exists_locEmb_eq η M₀ ⟨K.1, K.2.1, Finset.subset_univ _⟩ K.2.2
    (twistSub_le_twLocPart η M₀ hG hB K n c z.2)).choose_spec.2

theorem ιfun_add (K : Chart x) (z z' : ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    ιfun η M₀ n c hG hB K (z + z') = ιfun η M₀ n c hG hB K z + ιfun η M₀ n c hG hB K z' := by
  apply locEmb_injective η M₀ K.2.2
  change UT.toL _ = UT.toL _
  rw [map_add, UT.toL_add, ιfun_emb, ιfun_emb, ιfun_emb, Submodule.coe_add, single_add]

theorem ιfun_zero (K : Chart x) : ιfun η M₀ n c hG hB K 0 = 0 := by
  apply locEmb_injective η M₀ K.2.2
  change UT.toL _ = UT.toL _
  rw [map_zero, UT.toL_zero, ιfun_emb, Submodule.coe_zero, single_zero]

theorem cf_ιfun (K : Chart x) (z : ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    cf η M₀ n c K.1 K.2.2 (ιfun η M₀ n c hG hB K z) = z := by
  change (UT.toL (locEmb η M₀ K.1 K.2.2 (ιfun η M₀ n c hG hB K z))).coeff _ = _
  rw [ιfun_emb, coeff_single, Finsupp.single_eq_same]

theorem single_sum_zsmul {ι : Type*} (s : Finset ι) (a : ι → ℤ) (v : ι → Ω) (k : ℤ × ℤ) :
    single k (∑ j ∈ s, a j • v j) = ∑ j ∈ s, a j • single k (v j) := by
  have := map_sum (singleAddHom (R := Ω) k) (fun j => a j • v j) s
  simp only [map_zsmul] at this
  exact this

theorem ιfun_mem' {i : ℕ} (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (h : J.1.1 ⊆ support x)
    (z : ((G.twist (B.pow n)).twist (twistSys S x c)).sub (downI J h).1) :
    ιfun η M₀ n c hG hB (downI J h).1 z ∈ degLoc (twGraded η M₀) c J.1 :=
  ιfun_mem η M₀ n c hG hB (downI J h).1 z

theorem ιfun_emb' {i : ℕ} (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (h : J.1.1 ⊆ support x)
    (z : ((G.twist (B.pow n)).twist (twistSys S x c)).sub (downI J h).1) :
    UT.toL (locEmb η M₀ J.1.1 h (ιfun η M₀ n c hG hB (downI J h).1 z)) = single ((n : ℤ), c) (z : Ω) :=
  ιfun_emb η M₀ n c hG hB (downI J h).1 z

open Classical in

def Fmap (i : ℕ) (t : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i) :
    Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i :=
  fun J => if h : J.1.1 ⊆ support x then ιfun η M₀ n c hG hB (downI J h).1 (t (downI J h)) else 0

theorem Fmap_pos (i : ℕ) (t : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i)
    (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (h : J.1.1 ⊆ support x) :
    Fmap η M₀ n c hG hB i t J = ιfun η M₀ n c hG hB (downI J h).1 (t (downI J h)) :=
  dif_pos h

theorem Fmap_neg (i : ℕ) (t : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i)
    (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (h : ¬ J.1.1 ⊆ support x) :
    Fmap η M₀ n c hG hB i t J = 0 :=
  dif_neg h

theorem Fmap_add (i : ℕ) (t t' : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i) :
    Fmap η M₀ n c hG hB i (t + t') = Fmap η M₀ n c hG hB i t + Fmap η M₀ n c hG hB i t' := by
  funext J
  by_cases h : J.1.1 ⊆ support x
  · rw [Pi.add_apply, Fmap_pos η M₀ n c hG hB i _ J h, Fmap_pos η M₀ n c hG hB i _ J h,
      Fmap_pos η M₀ n c hG hB i _ J h, Pi.add_apply, ιfun_add]
    rfl
  · rw [Pi.add_apply, Fmap_neg η M₀ n c hG hB i _ J h, Fmap_neg η M₀ n c hG hB i _ J h,
      Fmap_neg η M₀ n c hG hB i _ J h, add_zero]

theorem Fmap_zero (i : ℕ) : Fmap η M₀ n c hG hB i 0 = 0 := by
  funext J
  by_cases h : J.1.1 ⊆ support x
  · rw [Fmap_pos η M₀ n c hG hB i _ J h, Pi.zero_apply, Pi.zero_apply, ιfun_zero]
    rfl
  · rw [Fmap_neg η M₀ n c hG hB i _ J h, Pi.zero_apply]

theorem Fmap_mem (i : ℕ) (t : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i) :
    Fmap η M₀ n c hG hB i t ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀))
      (degLoc (twGraded η M₀) c) i := by
  rw [Cech.Cdeg, Submodule.mem_pi]
  intro J _
  by_cases h : J.1.1 ⊆ support x
  · rw [Fmap_pos η M₀ n c hG hB i _ J h]
    exact ιfun_mem' η M₀ n c hG hB J h _
  · rw [Fmap_neg η M₀ n c hG hB i _ J h]
    exact Submodule.zero_mem _

theorem tval_d (i : ℕ) (t : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i)
    (K : Cech.Idx (support x) (i + 1)) :
    ((Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i t K : ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K.1)) : Ω) =
      ∑ j : K.1.1, Cech.sgn K.1.1 j • (t (Cech.face K j) : Ω) := by
  rw [Cech.d_apply, Submodule.coe_sum]
  rfl

theorem F_d (i : ℕ) (t : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i) :
    Fmap η M₀ n c hG hB (i + 1) (Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i t) =
      Cech.d (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) locResS i (Fmap η M₀ n c hG hB i t) := by
  funext J
  by_cases hJ : J.1.1 ⊆ support x
  · apply locEmb_injective η M₀ hJ
    have e1 : UT.toL (locEmb η M₀ J.1.1 hJ (Fmap η M₀ n c hG hB (i + 1)
        (Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i t) J)) =
        ∑ j : J.1.1, Cech.sgn J.1.1 j • single ((n : ℤ), c) ((t (Cech.face (downI J hJ) j)) : Ω) := by
      rw [Fmap_pos η M₀ n c hG hB (i + 1) _ J hJ, ιfun_emb', tval_d, single_sum_zsmul]
      rfl
    have e2 : UT.toL (locEmb η M₀ J.1.1 hJ
        (Cech.d (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) locResS i (Fmap η M₀ n c hG hB i t) J)) =
        ∑ j : J.1.1, Cech.sgn J.1.1 j • single ((n : ℤ), c) ((t (Cech.face (downI J hJ) j)) : Ω) := by
      rw [Cech.d_apply, map_sum, UT.toL_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hf : (Cech.face J j).1.1 ⊆ support x := (Cech.face_subset J j).trans hJ
      rw [map_zsmul, UT.toL_zsmul, locEmb_locResS η M₀ (Cech.face J j).1 J.1 hf hJ,
        Fmap_pos η M₀ n c hG hB i _ _ hf, ιfun_emb']
      rfl
    exact e1.trans e2.symm
  · have := twLocMod_subsingleton η M₀ hJ
    exact Subsingleton.elim _ _

def gm (i : ℕ) (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
    (K : Cech.Idx (support x) i) : Ω :=
  cf η M₀ n c (upI K).1.1 K.1.2.2 (s (upI K))

theorem gm_add (i : ℕ) (s s' : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
    (K : Cech.Idx (support x) i) : gm η M₀ n c i (s + s') K = gm η M₀ n c i s K + gm η M₀ n c i s' K :=
  map_add (cf η M₀ n c (upI K).1.1 K.1.2.2) _ _

theorem gm_zero (i : ℕ) (K : Cech.Idx (support x) i) : gm η M₀ n c i 0 K = 0 :=
  map_zero (cf η M₀ n c (upI K).1.1 K.1.2.2)

theorem gm_d (i : ℕ) (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
    (K : Cech.Idx (support x) (i + 1)) :
    gm η M₀ n c (i + 1) (Cech.d _ locResS i s) K = ∑ j : K.1.1, Cech.sgn K.1.1 j • gm η M₀ n c i s (Cech.face K j) := by
  rw [gm, Cech.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, cf_locResS η M₀ n c _ _ ((Cech.face_subset (upI K) j).trans K.1.2.2) K.1.2.2]
  rfl

theorem gm_Fmap (i : ℕ) (t : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i)
    (K : Cech.Idx (support x) i) : gm η M₀ n c i (Fmap η M₀ n c hG hB i t) K = t K := by
  rw [gm, Fmap_pos η M₀ n c hG hB i t (upI K) K.1.2.2]
  exact cf_ιfun η M₀ n c hG hB (downI (upI K) K.1.2.2).1 _

include hG hB in
theorem gm_mem (i : ℕ) {s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i}
    (hs : s ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) i)
    (K : Cech.Idx (support x) i) : gm η M₀ n c i s K ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K.1 := by
  rw [Cech.Cdeg, Submodule.mem_pi] at hs
  exact twLocPart_le_twistSub η M₀ hG hB K.1 n c
    (locGood_locEmb η M₀ (upI K).1 K.1.2.2 (hs (upI K) (Set.mem_univ _)) n)

def Gm (i : ℕ) (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
    (hs : s ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) i) :
    Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i :=
  fun K => ⟨gm η M₀ n c i s K, gm_mem η M₀ n c hG hB i hs K⟩

theorem Gm_d (i : ℕ) (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
    (hs : s ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) i)
    (hs' : Cech.d _ locResS i s ∈
      Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) (i + 1)) :
    Gm η M₀ n c hG hB (i + 1) (Cech.d _ locResS i s) hs' =
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i (Gm η M₀ n c hG hB i s hs) := by
  funext K
  apply Subtype.ext
  rw [tval_d]
  exact gm_d η M₀ n c i s K

theorem F_bdry (i : ℕ) (z : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i)
    (hz : z ∈ Cech.bdry (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
      ((G.twist (B.pow n)).twist (twistSys S x c)).res i) :
    Fmap η M₀ n c hG hB i z ∈ Cech.bdryDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀))
      (degLoc (twGraded η M₀) c) locResS i := by
  cases i with
  | zero =>
    have h0 : z = 0 := by
      change z ∈ (⊥ : Submodule S _) at hz
      exact (Submodule.mem_bot _).mp hz
    subst h0
    rw [Fmap_zero]
    exact Submodule.zero_mem _
  | succ i =>
    change z ∈ LinearMap.range _ at hz
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hz
    rw [F_d]
    exact Submodule.mem_map.mpr ⟨Fmap η M₀ n c hG hB i t, Fmap_mem η M₀ n c hG hB i t, rfl⟩

theorem G_bdry (i : ℕ) (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
    (hs : s ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) i)
    (hb : s ∈ Cech.bdryDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀))
      (degLoc (twGraded η M₀) c) locResS i) :
    Gm η M₀ n c hG hB i s hs ∈ Cech.bdry (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
      ((G.twist (B.pow n)).twist (twistSys S x c)).res i := by
  cases i with
  | zero =>
    have h0 : s = 0 := by
      change s ∈ (⊥ : Submodule (MvPolynomial (Fin (r + 1)) S) _) at hb
      exact (Submodule.mem_bot _).mp hb
    subst h0
    have : Gm η M₀ n c hG hB 0 0 hs = 0 := funext fun K => Subtype.ext (gm_zero η M₀ n c 0 K)
    rw [this]
    exact Submodule.zero_mem _
  | succ i =>
    obtain ⟨s', hs', rfl⟩ := Submodule.mem_map.mp hb
    rw [Gm_d η M₀ n c hG hB i s' hs' hs]
    exact LinearMap.mem_range_self _ _

end Split

end

end GroundTheory.Heights₂.Heights.Kleiman
