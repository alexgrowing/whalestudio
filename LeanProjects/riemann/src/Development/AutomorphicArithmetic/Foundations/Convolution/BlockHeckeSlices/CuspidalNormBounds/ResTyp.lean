import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GroundTheory.Automorphic GroundTheory.Automorphic.Reduction Matrix

private theorem lev_val {R : Type} [CommRing R] {r s : ℕ} (a : GL (Fin r) R) (b : GL (Fin s) R) :
    (lev R r s (a, b)).val = reindex finSumFinEquiv finSumFinEquiv (fromBlocks a.val 0 0 b.val) := by
  have : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := by
    ext (x | x) <;> simp
  rw [lev, GlobalTheory.SmGL.val_emb₂, this]

private theorem lev_euclid {L : Type} [NormedField L] {r s : ℕ} (a : GL (Fin r) L) (b : GL (Fin s) L)
    (ha : ∀ y, euclidNorm (y ᵥ* a.val) = euclidNorm y) (hb : ∀ y, euclidNorm (y ᵥ* b.val) = euclidNorm y)
    (y : Fin (r + s) → L) : euclidNorm (y ᵥ* (lev L r s (a, b)).val) = euclidNorm y := by
  have sq : ∀ {m : ℕ} {x z : Fin m → L}, euclidNorm x = euclidNorm z → ∑ i, ‖x i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := fun h =>
    (Real.sqrt_inj (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h
  have e1 : ∀ i, (y ᵥ* (lev L r s (a, b)).val) (Fin.castAdd s i) = ((fun j => y (Fin.castAdd s j)) ᵥ* a.val) i := by
    intro i
    simp [lev_val, vecMul, dotProduct, Fin.sum_univ_add]
  have e2 : ∀ i, (y ᵥ* (lev L r s (a, b)).val) (Fin.natAdd r i) = ((fun j => y (Fin.natAdd r j)) ᵥ* b.val) i := by
    intro i
    simp [lev_val, vecMul, dotProduct, Fin.sum_univ_add]
  rw [euclidNorm, euclidNorm, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [e1, e2]
  rw [sq (ha _), sq (hb _)]

private theorem lev_entries {L : Type} [Field L] (O : Subring L) {r s : ℕ} (a : GL (Fin r) L) (b : GL (Fin s) L)
    (ha : ∀ i j, a i j ∈ O) (hb : ∀ i j, b i j ∈ O) (x y : Fin (r + s)) : (lev L r s (a, b)).val x y ∈ O := by
  rw [lev_val, reindex_apply, submatrix_apply]
  rcases finSumFinEquiv.symm x with x | x <;> rcases finSumFinEquiv.symm y with y | y
  · exact ha x y
  · exact O.zero_mem
  · exact O.zero_mem
  · exact hb x y

theorem UpperTheory.ConvolutionTheory.BW.resTyp :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.ResTyp E := by
  intro E _ _ _ r s ρ
  have key : ∀ (k : KA E r) (k' : KA E s), lev (Ad E) r s ((k : GA E r), (k' : GA E s)) ∈ KA E (r + s) := by
    intro k k'
    obtain ⟨h1, h2⟩ := mem_maxCompact.1 k.2
    obtain ⟨h3, h4⟩ := mem_maxCompact.1 k'.2
    refine mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩
    · have e : infAt w (lev (Ad E) r s ((k : GA E r), (k' : GA E s))) = lev _ r s (infAt w k.1, infAt w k'.1) :=
        Slice1.map_lev (infEval w) _
      rw [e]
      exact lev_euclid _ _ (h1 w) (h3 w)
    · have e : finAt v (lev (Ad E) r s ((k : GA E r), (k' : GA E s))) = lev _ r s (finAt v k.1, finAt v k'.1) :=
        Slice1.map_lev (finEval v) _
      rw [e]
      obtain ⟨a1, a2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 (h2 v)
      obtain ⟨b1, b2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 (h4 v)
      refine (GLnLocal.mem_integralGL_iff _ _).2 ⟨lev_entries _ _ _ a1 b1, ?_⟩
      rw [← map_inv]
      exact lev_entries _ _ _ a2 b2
  let j : KA E r × KA E s →* KA E (r + s) :=
    ((lev (Ad E) r s).comp ((KA E r).subtype.prodMap (KA E s).subtype)).codRestrict _ fun k => key k.1 k.2
  have hj : Continuous j := Continuous.subtype_mk ((Slice1.continuous_lev (Ad E)).comp
    (continuous_subtype_val.prodMap continuous_subtype_val)) _
  refine ⟨⟨ρ.ρ.comp (j.comp (MonoidHom.inl _ _)), ρ.cont.comp (hj.comp (continuous_id.prodMk continuous_const)), ?_⟩,
    ⟨ρ.ρ.comp (j.comp (MonoidHom.inr _ _)), ρ.cont.comp (hj.comp (continuous_const.prodMk continuous_id)), ?_⟩, key⟩
  · funext k
    have h : lev (Ad E) r s ((k : GA E r), 1) ∈ KA E (r + s) := key k 1
    rw [resL, dif_pos h]
    rfl
  · funext k
    have h : lev (Ad E) r s (1, (k : GA E s)) ∈ KA E (r + s) := key 1 k
    rw [resR, dif_pos h]
    rfl
