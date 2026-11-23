import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.LocOver.TermLat

open GlobalTheory.HL

section Mat

variable {E : Type} [CommRing E] {m : ℕ}

theorem minor_tri (A B Z : Matrix (Fin m) (Fin m) E) (hA : ∀ i j, i < j → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) {l : ℕ} (hl : l ≤ m) :
    ((A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  set e := Fin.castLE hl with he
  have hsub : ∀ (X Y : Matrix (Fin m) (Fin m) E),
      (∀ (i j : Fin l) (p : Fin m), l ≤ (p : ℕ) → X (e i) p * Y p (e j) = 0) →
      (X * Y).submatrix e e = X.submatrix e e * Y.submatrix e e := by
    intro X Y hXY
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective hl) _ _ ?_ ?_
    · intro p hp
      apply hXY i j p
      by_contra hlt
      push_neg at hlt
      exact hp ⟨⟨p, hlt⟩, rfl⟩
    · intro p
      rfl
  have hdA : (A.submatrix e e).det = 1 := by
    rw [Matrix.det_of_lowerTriangular (A.submatrix e e)
      (fun i j hij => hA _ _ (by exact OrderDual.toDual_lt_toDual.1 hij))]
    simp [hA1]
  have hdB : (B.submatrix e e).det = 1 := by
    rw [Matrix.det_of_upperTriangular
      (show (B.submatrix e e).BlockTriangular id from fun i j hij => hB _ _ (by exact hij))]
    simp [hB1]
  rw [hsub (A * Z) B (fun i j p hp => by
      rw [hB p (e j) (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le j.2 hp)), mul_zero]),
    hsub A Z (fun i j p hp => by
      rw [hA (e i) p (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le i.2 hp)), zero_mul]),
    Matrix.det_mul, Matrix.det_mul, hdA, hdB, one_mul, mul_one]

end Mat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map M.L.cj

theorem h_sum_left {ι : Type} (s : Finset ι) (u : ι → V) (y : V) :
    H.h (∑ i ∈ s, u i) y = ∑ i ∈ s, H.h (u i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty]
    exact H.h_zero_left y
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]

theorem h_right_sum {ι : Type} [Fintype ι] (a : ι → E) (u : ι → V) (x : V) :
    H.h x (∑ i, a i • u i) = ∑ i, M.L.cj (a i) * H.h x (u i) := by
  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [H.h_smul_left, map_mul, ← H.h_herm]

theorem zhat_change (f f' g g' : Fin (r + 1) → V) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hg : ∀ j, g j = ∑ i, s i j • f i) (hg' : ∀ j, g' j = ∑ i, s' i j • f' i) :
    H.Zhat g g' = (Matrix.of fun a c => M.L.cj (s c a)) * H.Zhat f f' * s' := by
  ext a b
  simp only [HermSp.Zhat, Matrix.mul_apply, Matrix.of_apply, hg, hg']
  rw [h_sum_left]
  simp only [H.h_smul_left, h_right_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dl_change (f f' g g' : Fin (r + 1) → V) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1) (h0' : ∀ i j, j < i → s' i j = 0)
    (h1' : ∀ i, s' i i = 1) (hg : ∀ j, g j = ∑ i, s i j • f i) (hg' : ∀ j, g' j = ∑ i, s' i j • f' i)
    (l : ℕ) : H.Dl g g' l = H.Dl f f' l := by
  unfold HermSp.Dl
  split_ifs with hl
  · rw [zhat_change f f' g g' s s' hg hg']
    exact minor_tri _ _ _ (fun i j hij => by simp [h0 j i hij]) (fun i => by simp [h1]) h0' h1' hl
  · rfl

private theorem e_mem_lat_iff {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (Λ : Submodule M.L.O V) (v : V) :
    c.e v ∈ c.lat Λ ↔ v ∈ Λ := by
  constructor
  · intro h
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 h
    rwa [← c.e.injective hwv]
  · intro h
    exact Submodule.mem_map.2 ⟨v, h, rfl⟩

section Coordinates

variable {P : FPair H r} {S : Frames M.L r k} (c : Coord P S)

include c in

theorem selfDual_of (Λ : Submodule M.L.O V) (h : IsSD M.L S.Hm (c.lat Λ)) : H.IsSelfDual Λ := by
  obtain ⟨⟨hfg, hsp⟩, hd⟩ := h
  have hmem : ∀ v, c.e v ∈ c.lat Λ ↔ v ∈ Λ := e_mem_lat_iff c Λ
  refine ⟨?_, ?_, ?_⟩
  · exact Submodule.fg_of_fg_map_injective ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O) c.e.injective hfg
  · apply Submodule.map_injective_of_injective (f := (c.e : V →ₗ[E] S.V)) c.e.injective
    rw [Submodule.map_top, LinearEquiv.range, ← Submodule.span_image]
    exact hsp
  · intro x
    rw [← hmem x, ← hd (c.e x)]
    constructor
    · intro hx y hy
      have h1 := hx (c.e y) ((hmem y).2 hy)
      have h2 : hf M.L S.Hm (c.e y) (c.e x) = H.h y x := c.h_eq y x
      rw [h2] at h1
      rw [H.h_herm]
      exact cj_mem h1
    · intro hx w hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
      have h2 : hf M.L S.Hm (c.e y) (c.e x) = H.h y x := c.h_eq y x
      show hf M.L S.Hm (c.e y) (c.e x) ∈ M.L.O
      rw [h2, H.h_herm]
      exact cj_mem (hx y hy)

private theorem e_mem_inn_iff_exists_mkW_mem (c : Coord P S) (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) (v : V) :
    c.e v ∈ c.inn f L ↔ ∃ hv : v ∈ H.perp (H.X f), H.mkW f ⟨v, hv⟩ ∈ L := by
  rw [Coord.inn, e_mem_lat_iff]
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 h
    exact ⟨z.2, hz⟩
  · rintro ⟨hv, hL⟩
    exact Submodule.mem_map.2 ⟨⟨v, hv⟩, hL, rfl⟩

theorem lset_of (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hX : ∀ x, x ∈ H.X f ↔ c.e x ∈ S.spanTo g r)
    (hp : ∀ x, x ∈ H.perp (H.X f) ↔ c.e x ∈ perp M.L S.Hm (S.spanTo g r))
    (L : Submodule M.L.O (H.Wb f)) (Λ : Submodule M.L.O V) (n : V ≃ₗ[E] V) (hn : c.grp n ∈ S.Nof g)
    (e : c.lat Λ = c.grp n • S.stdLat g gs (c.inn f L))
    (h3 : ∀ x, x ∈ c.inn f L ↔ ∃ y ∈ S.stdLat g gs (c.inn f L),
      y ∈ perp M.L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) :
    (L : Set (H.Wb f)) = H.Lset Λ f := by
  have key : ∀ x : V, c.e x ∈ c.inn f L ↔
      ∃ y ∈ c.lat Λ, y ∈ perp M.L S.Hm (S.spanTo g r) ∧ y - c.e x ∈ S.spanTo g r := by
    intro x
    rw [h3, e]
    exact TermBasic.inner_smul S hn (c.e x)
  ext w
  obtain ⟨x0, rfl⟩ := Submodule.mkQ_surjective _ w
  simp only [HermSp.Lset, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hw
    obtain ⟨y, hy, hyp, hyx⟩ := (key x0).1 ((e_mem_inn_iff_exists_mkW_mem c f L x0).2 ⟨x0.2, hw⟩)
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
    have hvp : v ∈ H.perp (H.X f) := (hp v).2 hyp
    have hdiff : v - (x0 : V) ∈ H.X f := (hX _).2 (by rw [map_sub]; exact hyx)
    refine ⟨⟨v, hvp⟩, hv, ?_⟩
    exact (Submodule.Quotient.eq _).2 hdiff
  · rintro ⟨x, hxΛ, hxw⟩
    rw [← hxw]
    have hx := (key x).2 ⟨c.e x, (e_mem_lat_iff c Λ x).2 hxΛ, (hp x).1 x.2, by simp⟩
    obtain ⟨_, hL⟩ := (e_mem_inn_iff_exists_mkW_mem c f L x).1 hx
    exact hL

private theorem mem_isomG_of_mem_Nof_frames {S : Frames M.L r k} (g : Fin (r + 1) → S.V) {m : S.GLV} (hm : m ∈ S.Nof g) :
    m ∈ isomG M.L S.Hm := by
  simp only [Frames.Nof, Subgroup.mem_inf] at hm
  exact hm.1.1

theorem isom_of (g : Fin (r + 1) → S.V) {n : V ≃ₗ[E] V} (hn : c.grp n ∈ S.Nof g) (x y : V) :
    H.h (n x) (n y) = H.h x y := by
  have hI : c.grp n ∈ isomG M.L S.Hm := mem_isomG_of_mem_Nof_frames g hn
  have h1 := (show ∀ a b, hf M.L S.Hm (c.grp n a) (c.grp n b) = hf M.L S.Hm a b from hI) (c.e x) (c.e y)
  rw [CoordUnip.grp_apply, CoordUnip.grp_apply] at h1
  have h2 : hf M.L S.Hm (c.e (n x)) (c.e (n y)) = H.h (n x) (n y) := c.h_eq (n x) (n y)
  have h3 : hf M.L S.Hm (c.e x) (c.e y) = H.h x y := c.h_eq x y
  rw [← h2, ← h3]
  exact h1

theorem frame_of (Fr : FrameD H r) (g : Fin (r + 1) → S.V) (hgf : ∀ a, g a = c.e (Fr.f a))
    (hg : ∀ a (j : Fin r), hf M.L S.Hm (g a) (g j.castSucc) = 0) (hli : LinearIndependent E g)
    (n : V ≃ₗ[E] V) (hn : c.grp n ∈ S.Nof g) (Λ : Submodule M.L.O V)
    (htr : ∀ x, (x ∈ c.lat Λ ∧ x ∈ S.spanTo g (r + 1)) ↔
      x ∈ Submodule.span M.L.O ((fun b => c.grp n (g b)) '' {i | (i : ℕ) < r + 1}))
    (hT : Fr.T ∈ 𝒪[F]) (hT0 : Fr.T ≠ 0) : H.IsFrame Λ r (fun b => n (Fr.f b)) Fr.T := by
  have hfr : ∀ b, c.grp n (g b) = c.e (n (Fr.f b)) := fun b => by rw [hgf, CoordUnip.grp_apply]
  unfold HermSp.IsFrame HermSp.Prim
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hT, hT0⟩
  · intro a
    have ha : c.e (n (Fr.f a)) ∈ c.lat Λ :=
      ((htr _).2 (Submodule.subset_span ⟨a, a.2, hfr a⟩)).1
    exact (e_mem_lat_iff c Λ _).1 ha
  · have hli' : LinearIndependent E Fr.f := by
      have h1 : LinearIndependent E ((c.e : V →ₗ[E] S.V) ∘ Fr.f) := by
        convert hli using 1
        funext a
        exact (hgf a).symm
      exact LinearIndependent.of_comp _ h1
    exact hli'.map' (n : V →ₗ[E] V) n.ker
  · intro x hx hxs
    have hxS : c.e x ∈ S.spanTo g (r + 1) := by
      have h1 := Submodule.apply_mem_span_image_of_mem_span (c.e : V →ₗ[E] S.V) hxs
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      show c.e (n (Fr.f b)) ∈ S.spanTo g (r + 1)
      rw [← hfr b]
      exact (TermBasic.map_mem_iff hg hn (r + 1) (g b)).2 (TermBasic.self_mem S g b.2)
    have h2 := (htr (c.e x)).1 ⟨(e_mem_lat_iff c Λ x).2 hx, hxS⟩
    have h3 := Submodule.apply_mem_span_image_of_mem_span
      ((c.e.symm : S.V →ₗ[E] V).restrictScalars M.L.O) h2
    have h4 : ((c.e.symm : S.V →ₗ[E] V).restrictScalars M.L.O) (c.e x) = x := c.e.symm_apply_apply x
    rw [h4] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨_, ⟨b, _, rfl⟩, rfl⟩
    exact ⟨b, by simp [hfr]⟩
  · intro a b hab
    show H.h (n (Fr.f a)) (n (Fr.f b)) = 0
    rw [isom_of c g hn]
    exact Fr.h_iso a b hab
  · show H.h (n (Fr.f (Fin.last r))) (n (Fr.f (Fin.last r))) = -algebraMap F E Fr.T
    rw [isom_of c g hn]
    exact Fr.h_zz

include c in

theorem change_of (Fr : FrameD H r) (g : Fin (r + 1) → S.V) (hgf : ∀ a, g a = c.e (Fr.f a))
    (n : V ≃ₗ[E] V) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ j, c.grp n (g j) = ∑ i, s i j • g i) (j : Fin (r + 1)) :
    n (Fr.f j) = ∑ i, s i j • Fr.f i := by
  apply c.e.injective
  rw [← CoordUnip.grp_apply c n (Fr.f j), ← hgf j, hs j, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hgf i]

private theorem lat_img_eq_grp_smul_lat (c : Coord P S) (m : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    c.lat (img m Λ) = c.grp m • c.lat Λ := by
  ext x
  rw [TermBasic.mem_smul]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨c.e z, (e_mem_lat_iff c Λ z).2 hz, CoordUnip.grp_apply c m z⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨m z, Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
    exact (CoordUnip.grp_apply c m z).symm

theorem term_over (hM : M.OK) (c : Coord P S) (hP : P.RelG (theta M)) (d : Datum P) (t : Term V M r)
    (ht : IsTermOver P d t) :
    H.IsTerm t ∧ (d.L : Set (H.Wb P.A.f)) = H.Lset t.abelian₂ P.A.f ∧
      (d.L' : Set (H.Wb P.B.f)) = H.Lset t.abelian₂ P.B.f := by
  haveI := hM.loc
  haveI := hM.char0
  unfold LocNG.FPair.RelG at hP
  obtain ⟨-, hD, hG, -, -, -, hN⟩ := hP
  unfold LocNG.FPair.NormsOK at hN
  obtain ⟨hTA, hA0, hTB, hB0, hNg⟩ := hN
  unfold IsTermOver at ht
  obtain ⟨hT, hT', ⟨n, hn, hfA, hLam⟩, ⟨n', hn', hfB, hLam'⟩, hgg⟩ := ht
  have tr := CoordUnip.transport M hM H r k P S c
  have trA := CoordInnerFst.transport M hM H r k P S c
  have trB := CoordInnerSnd.transport M hM H r k P S c
  have hli := (FrameBasic.main M.L r k S).1
  have hnS : c.grp n ∈ S.Nof S.f := (tr.2.1 n).1 hn
  have hnS' : c.grp n' ∈ S.Nof S.f' := (tr.2.2.1 n').1 hn'
  have hinA : S.IsInner S.f S.es (c.inn P.A.f d.L) := (trA.2.1 d.L).1 d.hL
  have hinB : S.IsInner S.f' S.es' (c.inn P.B.f d.L') := (trB.2.1 d.L').1 d.hL'
  have spA := StdLat.stdLat_spec M.L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hinA
  have spB := StdLat.stdLat_spec M.L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hinB
  have hlatA : c.lat t.abelian₂ = c.grp n • S.stdLat S.f S.es (c.inn P.A.f d.L) := by
    rw [hLam, lat_img_eq_grp_smul_lat, trA.2.2.2 d.L]
  have hlatB : c.lat t.abelian₂ = c.grp n' • S.stdLat S.f' S.es' (c.inn P.B.f d.L') := by
    rw [hLam', lat_img_eq_grp_smul_lat, trB.2.2.2 d.L']
  have hgA : ∀ a (j : Fin r), hf M.L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    rw [S.gram]
    exact if_neg fun h => (Fin.castSucc_lt_last j).ne h.2
  have hgB : ∀ a (j : Fin r), hf M.L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    rw [S.gram']
    exact if_neg fun h => (Fin.castSucc_lt_last j).ne h.2
  have hfrA : H.IsFrame t.abelian₂ r t.f t.T := by
    rw [hfA, hT]
    exact frame_of c P.A S.f c.f_eq hgA (by simpa using hli.comp Sum.inl Sum.inl_injective) n hnS t.abelian₂
      (fun x => by rw [hlatA]; exact TermBasic.trace_smul hgA hnS (spA.2.1 (r + 1) le_rfl) x) hTA hA0
  have hfrB : H.IsFrame t.abelian₂ r t.f' t.T' := by
    rw [hfB, hT']
    exact frame_of c P.B S.f' c.f'_eq hgB (by simpa using hli.comp Sum.inr Sum.inr_injective) n' hnS' t.abelian₂
      (fun x => by rw [hlatB]; exact TermBasic.trace_smul hgB hnS' (spB.2.1 (r + 1) le_rfl) x) hTB hB0
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := FrameOnto.exists_matrix S S.f S.T S.gram (c.grp n) hnS
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' (c.grp n') hnS'
  have hDl : ∀ l, H.Dl t.f t.f' l = H.Dl P.A.f P.B.f l := fun l =>
    dl_change P.A.f P.B.f t.f t.f' s s' hs0 hs1 hs0' hs1'
      (fun j => by rw [hfA]; exact change_of c P.A S.f c.f_eq n s hs j)
      (fun j => by rw [hfB]; exact change_of c P.B S.f' c.f'_eq n' s' hs' j) l
  refine ⟨?_, ?_, ?_⟩
  · unfold HermSp.IsTerm
    refine ⟨?_, hfrA, hfrB, ?_, ?_, ?_⟩
    · exact selfDual_of c t.abelian₂ (by rw [hlatA]; exact TermBasic.isSD_smul S (mem_isomG_of_mem_Nof_frames S.f hnS) spA.1)
    · rw [hDl]
      exact hD
    · rw [show H.Gdet t.f t.f' t.T t.T' = H.Gdet P.A.f P.B.f P.A.T P.B.T by
        simp only [HermSp.Gdet, hDl, hT, hT']]
      exact hG
    · intro g hg
      obtain ⟨hu, hc⟩ := hNg g hg
      refine ⟨?_, ?_, (hgg g hg).1⟩
      · rw [hT, hT']
        exact hu
      · rw [hT, hT']
        exact hc
  · exact lset_of c P.A.f S.f S.es tr.2.2.2.2.2.1 tr.2.2.2.2.2.2.2.1 d.L t.abelian₂ n hnS hlatA spA.2.2
  · exact lset_of c P.B.f S.f' S.es' tr.2.2.2.2.2.2.1 tr.2.2.2.2.2.2.2.2 d.L' t.abelian₂ n' hnS' hlatB spB.2.2

end Coordinates

theorem datum_of_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → (∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → H.IsTerm t ∧ (d.L : Set (H.Wb P.A.f)) = H.Lset t.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset t.abelian₂ P.B.f) ∧ ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → H.Lset t.abelian₂ P.A.f = H.Lset t'.abelian₂ P.A.f → H.Lset t.abelian₂ P.B.f = H.Lset t'.abelian₂ P.B.f → (∀ g, M.split = some g → H.iotaGraph g ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩ = H.iotaGraph g ⟨t'.abelian₂, P.A.f, P.B.f, t'.T, t'.T'⟩) → d = d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hdim hP
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hdim hP
  refine ⟨fun d t ht => term_over hM c hP d t ht, ?_⟩
  intro d d' t t' ht ht' hA hB hio
  obtain ⟨-, hdA, hdB⟩ := term_over hM c hP d t ht
  obtain ⟨-, hdA', hdB'⟩ := term_over hM c hP d' t' ht'
  have h1 : d.L = d'.L := SetLike.coe_injective (by rw [hdA, hdA', hA])
  have h2 : d.L' = d'.L' := SetLike.coe_injective (by rw [hdB, hdB', hB])
  have h3 : d.io = d'.io := by
    cases hs : M.split with
    | none => rw [d.io_L hs, d'.io_L hs]
    | some g =>
      have e1 := ht
      have e2 := ht'
      unfold IsTermOver at e1 e2
      rw [← (e1.2.2.2.2 g hs).2, ← (e2.2.2.2.2 g hs).2]
      exact hio g hs
  rcases d with ⟨L1, L1', hL1, hL1', io1, hio1⟩
  rcases d' with ⟨L2, L2', hL2, hL2', io2, hio2⟩
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

end GlobalTheory.LocOver.TermLat
