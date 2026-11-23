import Development.EtaleCohomology.EtaleSheaves.LeafTensMonoPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafPreTensLocInjPf
open LateralTheory.E.LeafTensMonoPf LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem sec_sgl_zero (F : Shv R) {s : ℤ} (hs : s ≠ 0) {U : Scheme.{0}} (a : Sec ((sgl F).X s) U) : a = 0 := by
  have hZ : IsZero ((sgl F).X s) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hs
  have h1 : (𝟙 ((sgl F).X s)) = 0 := hZ.eq_of_src _ _
  have h2 : Sec.map (𝟙 ((sgl F).X s)) a = a := rfl
  rw [← h2, h1]
  rfl

theorem tens_zero_left (F : Shv R) {J : Cx R} {s t : ℤ} (hs : s ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl F).X s) U ⊗[ULift.{1} R] Sec (J.X t) U) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [sec_sgl_zero F hs a, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

abbrev p0 (w : ℤ) : {p : ℤ × ℤ // p.1 + p.2 = w} := ⟨(0, w), by simp⟩

theorem tens_single (F : Shv R) {J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens (sgl F) J U w) :
    x = DirectSum.of _ (p0 w) (x (p0 w)) := by
  classical
  ext p
  by_cases hp : p = p0 w
  · subst hp; simp
  · rw [DirectSum.of_eq_of_ne _ _ _ hp]
    have : p.1.1 ≠ 0 := by
      intro h; apply hp; apply Subtype.ext; ext
      · exact h
      · simp; have := p.2; omega
    exact tens_zero_left F this _

theorem tens_res_of {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p t) =
      DirectSum.of _ p (TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom t) := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  unfold Tens.res
  rw [DirectSum.lmap_lof]
  rfl

theorem lift_of {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.of _ p t) = TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2) t := by
  classical
  unfold Pair.lift
  exact DirectSum.toModule_lof (ULift.{1} R)
    (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t

end

section
variable {R : Type} [CommRing R]
theorem tens_res_comp {I J : Cx R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (z : Tens I J U w) :
    Tens.res (k ≫ g) w z = Tens.res k w (Tens.res g w z) := by
  classical
  have : (Tens.res (I := I) (J := J) (k ≫ g) w) = (Tens.res k w).comp (Tens.res g w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Tens.res]
  exact LinearMap.congr_fun this z
end

theorem LeafPreTensLocInj_of (hS : LeafTw0LocSplit) : LeafPreTensLocInj := by
  intro q _ i T τ hτ U w x hx
  classical
  obtain ⟨S, hS0⟩ := TensorProduct.exists_finset (x (p0 w))
  set a : Fin S.card → Sec ((sgl (tw q 0)).X 0) U := fun k => (S.equivFin.symm k).1.1 with ha
  set b : Fin S.card → Sec ((res _ (tw q i)).X w) U := fun k => (S.equivFin.symm k).1.2 with hb
  have hxp : x (p0 w) = ∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k := by
    rw [hS0, ← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp S.equivFin.symm (fun i : S => i.1.1 ⊗ₜ[ULift.{1} (ZMod q)] i.1.2)).symm
  have hx' : x = DirectSum.of _ (p0 w) (∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k) := by
    rw [← hxp]; exact tens_single _ x
  set y : Tens (res _ (tw q 0)) (res _ (tw q i)) U w :=
    DirectSum.of _ (p0 w) (∑ k, Sec.map ((resAug (tw q 0)).f 0) (a k) ⊗ₜ[ULift.{1} (ZMod q)] b k) with hydef
  have hy : τ.lift U w y = 0 := by
    rw [← hx, hx', hydef, lift_of, lift_of]
    simp [pre]
  refine loc_trans (hτ.2 U w y hy) ?_
  intro V g hg
  refine loc_trans (hS q V S.card (fun k => Sec.res g (a k))) ?_
  rintro W k ⟨e, c, hac, he⟩
  suffices h : Tens.res (k ≫ g) w x = 0 from
    ⟨⊤, GrothendieckTopology.top_mem _ W, fun W' k' _ => by dsimp only; rw [Category.assoc, tens_res_comp, h, map_zero]⟩
  set bb : Sec ((res _ (tw q i)).X w) W := ∑ j, c j • Sec.res (k ≫ g) (b j) with hbb
  have hres : Tens.res (k ≫ g) w x = DirectSum.of _ (p0 w) (e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by
    rw [hx', tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (a j) = c j • e
    rw [res_comp]; exact hac j
  have hy0 : Tens.res (k ≫ g) w y =
      DirectSum.of _ (p0 w) (Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by
    rw [hydef, tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (Sec.map ((resAug (tw q 0)).f 0) (a j)) = c j • Sec.map ((resAug (tw q 0)).f 0) e
    rw [res_map, res_comp, hac j]
    exact map_smul (((resAug (tw q 0)).f 0).hom.app (op W)).hom (c j) e
  have hg0 : Tens.res (k ≫ g) w y = 0 := by rw [tens_res_comp, hg, map_zero]
  have ht : Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb = 0 :=
    DirectSum.of_injective (p0 w) (hy0.symm.trans (hg0.trans (map_zero _).symm))
  rw [hres]
  rcases he with he | ⟨r, hr⟩
  · rw [he, TensorProduct.zero_tmul, map_zero]
  · have hbb0 : bb = 0 := by
      have := congrArg (fun z => TensorProduct.lid (ULift.{1} (ZMod q)) _ (TensorProduct.map r LinearMap.id z)) ht
      simpa [hr] using this
    rw [hbb0, TensorProduct.tmul_zero, map_zero]

end LateralTheory.E.LeafPreTensLocInjPf
