import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhDetZpowMem

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      exact (not_le.mpr hc) (hm.2.trans (hmu hmt))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega
  · intro h
    have hsub : Finset.Iic t ⊆ (univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ m, h.trans (hmu hm)⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega

lemma qh_le_last [NeZero n] (a : Fin n) : a ≤ lastIdx n := by
  rw [Fin.le_iff_val_le_val]
  show a.val ≤ n - 1
  have := a.isLt
  omega

lemma qh_count [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) :
    ((TCols mu).filter (fun c => t.val < colH mu c)).card = (mu t - mu (lastIdx n)).toNat := by
  have h0 : mu t ≤ mu 0 := hmu (by first | exact Fin.zero_le _ | (rw [Fin.le_iff_val_le_val]; simp))
  have hset : (TCols mu).filter (fun c => t.val < colH mu c) =
      Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    simp only [Finset.mem_filter, qh_lt_colH_iff hmu, TCols, Finset.mem_Ioc]
    exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hh.2.trans h0⟩, hh.2⟩⟩
  rw [hset, Int.card_Ioc]

lemma qh_weight_sum [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun _ : Fin n => mu (lastIdx n)) +
      ∑ c : ↥(TCols mu), (fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0) = mu := by
  funext a
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [Finset.sum_coe_sort (TCols mu) (fun c => if a.val < colH mu c then (1 : ℤ) else 0),
    Finset.sum_boole, qh_count hmu a,
    Int.toNat_of_nonneg (sub_nonneg.mpr (hmu (qh_le_last a)))]
  ring

lemma qh_mapCoord_alg (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) R (algebraMap _ _ P) = algebraMap _ _ (MvPolynomial.map (Int.castRingHom R) P) := by
  first
    | (rw [mapCoord, IsLocalization.Away.AwayMap.lift_eq]; try rfl; done)
    | (rw [mapCoord, IsLocalization.Away.lift_eq]; try rfl; done)
    | (simp [mapCoord]; done)
    | (unfold mapCoord; exact IsLocalization.lift_eq _ _)

lemma qh_mapCoord_detU (z : ℤ) :
    mapCoord R ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((qhDet R n ^ z : (GLCoord R n)ˣ) : GLCoord R n) := by
  have h1 : Units.map (mapCoord (n := n) R).toMonoidHom (detU n) = qhDet R n := by
    apply Units.ext
    rw [Units.coe_map, qhDet_val]
    show mapCoord (n := n) R (algebraMap _ _ (genMat ℤ n).det) = _
    rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R)) (genMat ℤ n),
      genMat_map_coord]
  rw [← h1, ← map_zpow (Units.map (mapCoord (n := n) R).toMonoidHom) (detU n) z, Units.coe_map]
  try rfl

lemma qh_can_emb [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have hmem : ∀ x : Fin (colH mu c), Fin.castLE (colH_le mu c) x ∈ (canT mu c).1 := by
    intro x
    first
      | (simp only [canT, Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨x, rfl⟩)
      | simp [canT]
  have hmono : StrictMono (Fin.castLE (colH_le mu c)) := by
    intro x y hxy
    rw [Fin.lt_iff_val_lt_val] at hxy ⊢
    exact hxy
  exact (congrFun (Finset.orderEmbOfFin_unique (canT mu c).2 hmem hmono) a).symm

lemma qh_mapCoord_minor [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (S : Finset (Fin n))
    (hS : S.card = colH mu c) :
    mapCoord R (minorC (canT mu c).1 S (canT mu c).2 hS) =
      qhN R (colH mu c) (colH_le mu c) (fun q => S.orderEmbOfFin hS q) := by
  unfold minorC qhN
  rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R))]
  congr 2
  ext p q
  first
    | (simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, genMat, MvPolynomial.map_X,
        qh_can_emb]; done)
    | simp [genMat, qh_can_emb]

lemma qh_mapCoord_brk [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord R (brk mu I) = ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) *
      ∏ c : ↥(TCols mu), qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q) := by
  first
    | (simp only [brk, TMat]
       rw [map_mul, map_prod, qh_mapCoord_detU]
       congr 1
       refine Finset.prod_congr rfl (fun c _ => ?_)
       exact qh_mapCoord_minor mu c _ _)
    | (simp only [brk, TMat, map_mul, map_prod, qh_mapCoord_detU,
        qh_mapCoord_minor])

lemma qh_brk_mem [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    mapCoord R (brk mu I) ∈ inducedSections R mu := by
  rw [qh_mapCoord_brk]
  have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) (mu (lastIdx n)))
    (qh_prod_mem (R := R) (Finset.univ : Finset ↥(TCols mu))
      (fun c => qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q))
      (fun c => fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0)
      (fun c _ => qh_N_mem (R := R) (colH mu c) (colH_le mu c) _))
  first
    | (rw [qh_weight_sum hmu] at h; exact h)
    | (convert h using 2; exact (qh_weight_sum hmu).symm)

lemma qh_equiv_of_count {α β : Type} [Fintype α] [Fintype β] (f : α → ℕ) (g : β → ℕ)
    (hf : ∀ a, 0 < f a) (hg : ∀ b, 0 < g b)
    (h : ∀ t, (univ.filter fun a => t < f a).card = (univ.filter fun b => t < g b).card) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  have hfib : ∀ k : ℕ, (univ.filter fun a => f a = k).card = (univ.filter fun b => g b = k).card := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h1 : (univ.filter fun a => f a = 0) = ∅ := by
        ext a
        simp [(hf a).ne']
      have h2 : (univ.filter fun b => g b = 0) = ∅ := by
        ext b
        simp [(hg b).ne']
      rw [h1, h2, Finset.card_empty, Finset.card_empty]
    · have key : ∀ {γ : Type} [Fintype γ] (u : γ → ℕ), (univ.filter fun x => u x = k).card
          = (univ.filter fun x => k - 1 < u x).card - (univ.filter fun x => k < u x).card := by
        intro γ _ u
        have hsplit : (univ.filter fun x => k - 1 < u x) =
            (univ.filter fun x => u x = k) ∪ (univ.filter fun x => k < u x) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          constructor
          · intro hx
            omega
          · intro hx
            omega
        have hdisj : Disjoint (univ.filter fun x => u x = k) (univ.filter fun x => k < u x) := by
          rw [Finset.disjoint_filter]
          intro x _ hx
          omega
        rw [hsplit, Finset.card_union_of_disjoint hdisj]
        omega
      rw [key f, key g, h (k - 1), h k]
  have hcard : ∀ k : ℕ, Fintype.card {a // f a = k} = Fintype.card {b // g b = k} := by
    intro k
    first
      | (rw [Fintype.card_subtype, Fintype.card_subtype]; exact hfib k)
      | simpa [Fintype.card_subtype] using hfib k
  let e : α ≃ β := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun k => Fintype.equivOfCardEq (hcard k)).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨e, fun a => ?_⟩
  exact (Fintype.equivOfCardEq (hcard (f a)) ⟨a, rfl⟩).2

lemma qh_N_normal (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) :
    ∃ (ε : R) (S : {S : Finset (Fin n) // S.card = s}),
      qhN R s hs J = ε • qhN R s hs (fun q => S.1.orderEmbOfFin S.2 q) := by
  classical
  by_cases hJ : Function.Injective J
  · obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin n), S = Finset.univ.image J := ⟨_, rfl⟩
    have hS : S.card = s := by
      rw [hSdef, Finset.card_image_of_injective _ hJ, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ q, J q ∈ S := by
      intro q
      rw [hSdef]
      exact Finset.mem_image_of_mem J (Finset.mem_univ q)
    let τ : Fin s → Fin s := fun q => (S.orderIsoOfFin hS).symm ⟨J q, hmem q⟩
    have hτ : ∀ q, S.orderEmbOfFin hS (τ q) = J q := by
      intro q
      rw [← Finset.coe_orderIsoOfFin_apply]
      show (((S.orderIsoOfFin hS) ((S.orderIsoOfFin hS).symm ⟨J q, hmem q⟩)) : Fin n) = J q
      rw [OrderIso.apply_symm_apply]
    have hτinj : Function.Injective τ := by
      intro a b hab
      apply hJ
      rw [← hτ a, ← hτ b, hab]
    let σ : Equiv.Perm (Fin s) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
    have hσ : ∀ q, S.orderEmbOfFin hS (σ q) = J q := fun q => hτ q
    refine ⟨((Equiv.Perm.sign σ : ℤ) : R), ⟨S, hS⟩, ?_⟩
    have hM : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q)) =
        (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (S.orderEmbOfFin hS q)).submatrix id σ := by
      ext p q
      simp only [Matrix.submatrix_apply, Matrix.of_apply, id, hσ]
    have hdet : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q)).det =
        ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin n) R) *
          (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (S.orderEmbOfFin hS q)).det := by
      rw [hM]
      first
        | exact Matrix.det_permute' σ _
        | rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.det_permute, Matrix.det_transpose]
    unfold qhN
    rw [hdet]
    first
      | (simp only [map_mul, map_intCast, Algebra.smul_def]; done)
      | (simp only [map_mul, map_intCast, Algebra.smul_def]; rfl)
      | (rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]; try rfl; done)
      | simp [Algebra.smul_def]
  · have hex : ∃ a b, J a = J b ∧ a ≠ b := by
      by_contra hcon
      push_neg at hcon
      exact hJ (fun a b h => hcon a b h)
    obtain ⟨a, b, hab, hne⟩ := hex
    refine ⟨0, ⟨(Finset.univ : Finset (Fin s)).map (Fin.castLEEmb hs), by simp⟩, ?_⟩
    have h0 : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q)).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.of_apply, hab])
    first
      | (rw [zero_smul]; unfold qhN; rw [h0, map_zero])
      | (simp only [zero_smul]; unfold qhN; rw [h0, map_zero])

lemma qh_N_full (S : Finset (Fin n)) (hS : S.card = n) :
    qhN R n le_rfl (fun q => S.orderEmbOfFin hS q) = ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) := by
  have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS, Fintype.card_fin])
  have hid : ∀ q, S.orderEmbOfFin hS q = q := by
    intro q
    have hu := Finset.orderEmbOfFin_unique hS (f := id) (fun x => by rw [hSu]; exact Finset.mem_univ _) strictMono_id
    exact (congrFun hu q).symm
  have hc : ∀ p : Fin n, Fin.castLE (le_refl n) p = p := fun p => Fin.ext rfl
  unfold qhN
  rw [qhDet_val]
  congr 2
  ext p q
  first
    | (simp only [Matrix.of_apply, hid, hc]; done)
    | simp [genMat, hid, hc]

end Formalism.InvariantFactorPaths.ColumnFamilies
