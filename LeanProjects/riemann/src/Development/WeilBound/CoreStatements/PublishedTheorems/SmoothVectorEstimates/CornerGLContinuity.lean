import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace CornerGLContinuity

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem glmap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : GL (Fin a) R) :
    GeneralLinearGroup.map (g.comp f) x = GeneralLinearGroup.map g (GeneralLinearGroup.map f x) := by
  ext i j; rfl

theorem cornerGL_blkU {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (k : ℕ) (y : UnipotentBlockColumnIndex a k k → R) :
    cornerGL a s (blkU y) = blkU fun t => s (y t) := by
  apply Units.ext
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) +
    s ((1 + posM Subtype.val y) i j) = (1 + posM Subtype.val fun t => s (y t)) i j
  simp only [posM, Matrix.add_apply, Matrix.sum_apply, map_add, map_sum, Matrix.single_apply,
    apply_ite s, map_zero]
  abel

theorem cLoc_eq (w : Pl E) (x : GA E a) :
    cLoc w x = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) :=
  glmap_comp _ _ x

theorem gf_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun w => ?_)
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x i j) (H w)

theorem locGL_mul_comm {v : Pl E} (h : GL (Fin a) (v.adicCompletion E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E v) k = 1) : locGL E a v h * k = k * locGL E a v h := by
  refine gf_ext fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw
    rw [hk, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hw, mul_one, one_mul]

open Classical in
theorem map_pLoc_prod (g : GA E a) (v : Pl E) : ∀ l : List (Pl E), l.Nodup →
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E a w (cLoc w g)).prod =
      if v ∈ l then cLoc v g else 1
  | [], _ => by simp
  | w :: l, h => by
    rw [List.map_cons, List.prod_cons, map_mul, map_pLoc_prod g v l (List.nodup_cons.1 h).2]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 h).1, mul_one]
      simp
    · rw [pLoc_locGL_of_ne hv, one_mul]
      simp [hv]

theorem continuous_glmap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL' {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

end CornerGLContinuity

open CornerGLContinuity in
theorem standard_stabiliser_bound : G0 := by
  intro E _ _ _ a
  have hpInf : Continuous (pInf E) :=
    (continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        (continuous_apply w)).comp continuous_fst
  have hpLoc : ∀ w : Pl E, Continuous (pLoc E w) := fun w =>
    RestrictedProduct.continuous_eval (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) w
  have hfin : Continuous (finGL E a) :=
    continuous_cornerGL' _ (continuous_const.prodMk continuous_id :
      Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  have hinf : Continuous (infGL E a) :=
    continuous_cornerGL' _ ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  refine ⟨fun y => pInf_infGL y, fun w y => ?_, fun w u => pInf_finGL _, fun w u => ?_,
    fun w v u hvw => ?_, fun g h h1 h2 => ?_, fun g hg y => ?_, fun w g hg u => ?_,
    fun k y => cornerGL_blkU _ k y, fun w k y => ?_, fun S g => ?_, ?_, fun w => ?_, fun w => ?_, hinf⟩
  · rw [cLoc_eq, pFin_infGL, map_one]
  · rw [cLoc_eq, fl, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL]
  · rw [cLoc_eq, fl, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL_of_ne hvw]
  · exact ga_ext h1 (gf_ext fun w => by rw [← cLoc_eq, ← cLoc_eq]; exact h2 w)
  · have hg' : GeneralLinearGroup.map (pInf E) g = 1 := hg
    exact ga_ext (by rw [map_mul, map_mul, hg', pInf_infGL, one_mul, mul_one])
      (by rw [map_mul, map_mul, pFin_infGL, one_mul, mul_one])
  · have hg' : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) = 1 := by
      rw [← cLoc_eq]; exact hg
    exact ga_ext (by rw [map_mul, map_mul, fl, MonoidHom.comp_apply, pInf_finGL, one_mul, mul_one])
      (by rw [map_mul, map_mul, fl, MonoidHom.comp_apply, pFin_finGL]; exact (locGL_mul_comm u hg').symm)
  · rw [fl, MonoidHom.comp_apply, locGL, cornerGL_blkU, finGL, cornerGL_blkU]
  · refine ⟨infGL E a (cInf g) * finGL E a (S.toList.map fun w => locGL E a w (cLoc w g)).prod, ?_, ?_, ?_⟩
    · change GeneralLinearGroup.map (pInf E) _ = _
      rw [map_mul, pInf_infGL, pInf_finGL, mul_one]
    · intro w hw
      rw [cLoc_eq, map_mul, map_mul, pFin_infGL, pFin_finGL, map_one, one_mul,
        map_pLoc_prod g w _ S.nodup_toList, if_pos (Finset.mem_toList.2 hw)]
    · intro w hw
      rw [cLoc_eq, map_mul, map_mul, pFin_infGL, pFin_finGL, map_one, one_mul,
        map_pLoc_prod g w _ S.nodup_toList, if_neg (fun h => hw (Finset.mem_toList.1 h))]
  · exact continuous_glmap _ hpInf
  · exact continuous_glmap _ ((hpLoc w).comp continuous_snd)
  · exact hfin.comp (continuous_cornerGL' _ (CuspSub.continuous_sLoc w))

end PositivityTheory.jumpWindows

end
