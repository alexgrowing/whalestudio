import Mathlib

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.Doubling

variable {E : Type} [Field E] {r : ℕ}

def conjSub (c : E ≃+* E) (S : Submodule E (Fin r → E)) : Submodule E (Fin r → E) where
  carrier := {w | (fun i => c (w i)) ∈ S}
  add_mem' := by
    intro a b ha hb
    have := S.add_mem ha hb
    simpa [Set.mem_setOf_eq, Pi.add_def] using this
  zero_mem' := by
    have h0 : (fun i => c ((0 : Fin r → E) i)) = 0 := by funext i; simp
    change (fun i => c ((0 : Fin r → E) i)) ∈ S
    rw [h0]
    exact S.zero_mem
  smul_mem' := by
    intro t a ha
    have := S.smul_mem (c t) ha
    simpa [Set.mem_setOf_eq, Pi.smul_def] using this

theorem mem_conjSub (c : E ≃+* E) (S : Submodule E (Fin r → E)) (w : Fin r → E) :
    w ∈ conjSub c S ↔ (fun i => c (w i)) ∈ S := ⟨fun h => h, fun h => h⟩

private theorem conj_mem_lemma (c : E ≃+* E) (hc : ∀ x, c (c x) = x)
    (S : Submodule E (Fin r → E)) (w : Fin r → E) :
    (fun i => c (w i)) ∈ conjSub c S ↔ w ∈ S := by
  rw [mem_conjSub]
  simp only [hc]

theorem finrank_conjSub (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (S : Submodule E (Fin r → E)) :
    Module.finrank E (conjSub c S) = Module.finrank E S := by
  let j : S ≃+ conjSub c S :=
    { toFun := fun x => ⟨fun i => c (x.1 i), (conj_mem_lemma c hc S x.1).2 x.2⟩
      invFun := fun y => ⟨fun i => c (y.1 i), (mem_conjSub c S y.1).1 y.2⟩
      left_inv := fun x => Subtype.ext (funext fun i => hc (x.1 i))
      right_inv := fun y => Subtype.ext (funext fun i => hc (y.1 i))
      map_add' := fun x y => Subtype.ext (funext fun i => map_add c (x.1 i) (y.1 i)) }
  have hr : Module.rank E S = Module.rank E (conjSub c S) :=
    rank_eq_of_equiv_equiv (c : E → E) j c.bijective
      (fun t x => Subtype.ext (funext fun i => map_mul c t (x.1 i)))
  exact (congrArg Cardinal.toNat hr).symm

theorem row_apply (c : E ≃+* E) (J : Matrix (Fin r) (Fin r) E) (x v : Fin r → E) :
    (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) v () =
      (fun i => c (x i)) ⬝ᵥ J.mulVec v := by
  rw [Matrix.toLin'_apply, Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.of_apply]

theorem mem_orth (c : E ≃+* E) (J : Matrix (Fin r) (Fin r) E) (S : Submodule E (Fin r → E))
    (v : Fin r → E) :
    v ∈ (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)))
      ↔ ∀ x ∈ S, (fun i => c (x i)) ⬝ᵥ J.mulVec v = 0 := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  rw [← row_apply c J x v]
  exact ⟨fun h => congrFun h (), fun h => funext fun u => by cases u; exact h⟩

theorem finrank_orth (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (J : Matrix (Fin r) (Fin r) E)
    (hJ : J.det ≠ 0) (S : Submodule E (Fin r → E)) :
    Module.finrank E
      (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) :
        Submodule E (Fin r → E)) + Module.finrank E S = r := by
  classical
  set T := conjSub c S
  have hTS : Module.finrank E T = Module.finrank E S := finrank_conjSub c hc S
  have hunit : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 (isUnit_iff_ne_zero.2 hJ)
  set Ψ : (Fin r → E) →ₗ[E] Module.Dual E (Fin r → E) :=
    (dotProductEquiv E (Fin r)).toLinearMap ∘ₗ J.vecMulLinear
  have hΨ : Function.Injective Ψ :=
    (dotProductEquiv E (Fin r)).injective.comp (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  have hΨv : ∀ w v, Ψ w v = w ⬝ᵥ J.mulVec v := fun w v => by
    simp [Ψ, Matrix.dotProduct_mulVec]
  have hO : (⨅ x ∈ S, LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) :
      Submodule E (Fin r → E)) = (T.map Ψ).dualCoannihilator := by
    ext v
    rw [mem_orth, Submodule.mem_dualCoannihilator]
    constructor
    · rintro h φ ⟨w, hw, rfl⟩
      rw [hΨv]
      have hw' := (mem_conjSub c S w).1 hw
      have := h _ hw'
      simpa only [hc] using this
    · intro h x hx
      have hx' : (fun i => c (x i)) ∈ T := by
        rw [mem_conjSub]; simpa only [hc] using hx
      have := h _ ⟨_, hx', rfl⟩
      rwa [hΨv] at this
  have hW : Module.finrank E (T.map Ψ) = Module.finrank E T :=
    (Submodule.equivMapOfInjective Ψ hΨ T).finrank_eq.symm
  have key := Subspace.finrank_add_finrank_dualCoannihilator_eq (T.map Ψ)
  rw [Module.finrank_fin_fun, hW, hTS] at key
  rw [hO]
  omega

theorem finrank_map_fst (Y : Submodule E ((Fin r → E) × (Fin r → E))) :
    Module.finrank E (Y.map (LinearMap.fst E _ _)) +
      Module.finrank E (Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E))) = Module.finrank E Y := by
  set f := (LinearMap.fst E (Fin r → E) (Fin r → E)).domRestrict Y with hf
  set g : Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E)) →ₗ[E] Y :=
    LinearMap.codRestrict Y ((LinearMap.inr E (Fin r → E) (Fin r → E)).comp (Submodule.subtype _))
      (fun w => w.2) with hg
  have hinj : Function.Injective g := by
    intro u w huw
    have h := congrArg (fun y : Y => (y : (Fin r → E) × (Fin r → E)).2) huw
    exact Subtype.ext h
  have hrange : LinearMap.range g = LinearMap.ker f := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hy
      have h1 : (y : (Fin r → E) × (Fin r → E)).1 = 0 := hy
      have hy' : (LinearMap.inr E (Fin r → E) (Fin r → E)) (y : (Fin r → E) × (Fin r → E)).2 =
          (y : (Fin r → E) × (Fin r → E)) := by
        exact Prod.ext h1.symm rfl
      refine ⟨⟨(y : (Fin r → E) × (Fin r → E)).2, ?_⟩, ?_⟩
      · rw [Submodule.mem_comap, hy']
        exact y.2
      · exact Subtype.ext hy'
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_domRestrict, ← hrange, LinearMap.finrank_range_of_inj hinj] at key
  exact key

theorem finrank_map_snd (Y : Submodule E ((Fin r → E) × (Fin r → E))) :
    Module.finrank E (Y.map (LinearMap.snd E _ _)) +
      Module.finrank E (Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E))) = Module.finrank E Y := by
  set f := (LinearMap.snd E (Fin r → E) (Fin r → E)).domRestrict Y with hf
  set g : Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E)) →ₗ[E] Y :=
    LinearMap.codRestrict Y ((LinearMap.inl E (Fin r → E) (Fin r → E)).comp (Submodule.subtype _))
      (fun w => w.2) with hg
  have hinj : Function.Injective g := by
    intro u w huw
    have h := congrArg (fun y : Y => (y : (Fin r → E) × (Fin r → E)).1) huw
    exact Subtype.ext h
  have hrange : LinearMap.range g = LinearMap.ker f := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rfl
    · intro hy
      have h1 : (y : (Fin r → E) × (Fin r → E)).2 = 0 := hy
      have hy' : (LinearMap.inl E (Fin r → E) (Fin r → E)) (y : (Fin r → E) × (Fin r → E)).1 =
          (y : (Fin r → E) × (Fin r → E)) := by
        exact Prod.ext rfl h1.symm
      refine ⟨⟨(y : (Fin r → E) × (Fin r → E)).1, ?_⟩, ?_⟩
      · rw [Submodule.mem_comap, hy']
        exact y.2
      · exact Subtype.ext hy'
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_domRestrict, ← hrange, LinearMap.finrank_range_of_inj hinj] at key
  exact key

private theorem conj_single_lemma (c : E ≃+* E) (i : Fin r) :
    (fun k => c ((Pi.single i (1 : E) : Fin r → E) k)) = (Pi.single i (1 : E) : Fin r → E) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem isometry_matrix (c : E ≃+* E) (J g : Matrix (Fin r) (Fin r) E)
    (h : ∀ x x' : Fin r → E, (fun i => c (x i)) ⬝ᵥ J.mulVec x' =
      (fun i => c ((g.mulVec x) i)) ⬝ᵥ J.mulVec (g.mulVec x')) :
    (g.map c).transpose * J * g = J := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [conj_single_lemma c i] at h1
  simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at h1
  rw [h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct,
    Matrix.mulVec, Matrix.col_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)

theorem maximal_isotropic_doubled (E : Type) [Field E] (c : E ≃+* E) (r : ℕ)
    (J : Matrix (Fin r) (Fin r) E) (hc : ∀ x, c (c x) = x) (hJ : J.det ≠ 0)
    (_hJh : J.transpose.map c = J) (Y : Submodule E ((Fin r → E) × (Fin r → E)))
    (hY : Module.finrank E Y = r)
    (hiso : ∀ y ∈ Y, ∀ y' ∈ Y, (fun i => c (y.1 i)) ⬝ᵥ J.mulVec y'.1 =
      (fun i => c (y.2 i)) ⬝ᵥ J.mulVec y'.2) :
    (Module.finrank E (Y.comap (LinearMap.inl E _ _)) =
        Module.finrank E (Y.comap (LinearMap.inr E _ _))) ∧
      Y.map (LinearMap.fst E _ _) = ⨅ x ∈ Y.comap (LinearMap.inl E _ _),
        LinearMap.ker ((Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j))) ∧
      (Y.comap (LinearMap.inl E _ _) = ⊥ ↔ ∃ g : GL (Fin r) E,
        ((g : Matrix (Fin r) (Fin r) E).map c).transpose * J * (g : Matrix (Fin r) (Fin r) E) = J ∧
          ∀ y, y ∈ Y ↔ y.2 = (g : Matrix (Fin r) (Fin r) E).mulVec y.1) := by
  classical
  set A := Y.comap (LinearMap.inl E (Fin r → E) (Fin r → E)) with hA
  set B := Y.comap (LinearMap.inr E (Fin r → E) (Fin r → E)) with hB
  have memA : ∀ a, a ∈ A ↔ ((a, 0) : (Fin r → E) × (Fin r → E)) ∈ Y := fun a => by
    rw [hA, Submodule.mem_comap, LinearMap.inl_apply]
  have memB : ∀ b, b ∈ B ↔ (((0 : Fin r → E), b) : (Fin r → E) × (Fin r → E)) ∈ Y := fun b => by
    rw [hB, Submodule.mem_comap, LinearMap.inr_apply]
  have hfst := finrank_map_fst Y
  have hsnd := finrank_map_snd Y
  rw [← hB, hY] at hfst
  rw [← hA, hY] at hsnd
  have hoA := finrank_orth c hc J hJ A
  have hoB := finrank_orth c hc J hJ B
  have le1 : Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) ≤ ⨅ x ∈ A,
      LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) := by
    rintro v ⟨y, hy, rfl⟩
    rw [mem_orth]
    intro a ha
    have := hiso _ ((memA a).1 ha) y hy
    simpa using this
  have le2 : Y.map (LinearMap.snd E (Fin r → E) (Fin r → E)) ≤ ⨅ x ∈ B,
      LinearMap.ker (Matrix.toLin' (Matrix.of fun (_ : Unit) j => ∑ i, c (x i) * J i j)) := by
    rintro v ⟨y, hy, rfl⟩
    rw [mem_orth]
    intro b hb
    have := hiso _ ((memB b).1 hb) y hy
    simpa using this.symm
  have d1 := Submodule.finrank_mono le1
  have d2 := Submodule.finrank_mono le2
  have hAB : Module.finrank E A = Module.finrank E B := by omega
  refine ⟨hAB, Submodule.eq_of_le_of_finrank_eq le1 (by omega), ?_⟩
  constructor
  · intro hA0
    have hA0' : Module.finrank E A = 0 := by rw [hA0]; exact finrank_bot E (Fin r → E)
    have hB0 : B = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hP1 : Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) = ⊤ :=
      Submodule.eq_of_le_of_finrank_eq le_top (by rw [finrank_top, Module.finrank_fin_fun]; omega)
    let f : Y →ₗ[E] (Fin r → E) := (LinearMap.fst E (Fin r → E) (Fin r → E)).comp Y.subtype
    have hf : ∀ y : Y, f y = (y : (Fin r → E) × (Fin r → E)).1 := fun y => rfl
    have finj : Function.Injective f := by
      intro y y' hyy
      rw [hf, hf] at hyy
      have hd : (y : (Fin r → E) × (Fin r → E)) - y' ∈ Y := Y.sub_mem y.2 y'.2
      have h2 : ((y : (Fin r → E) × (Fin r → E)) - y').2 ∈ B := by
        rw [memB]
        convert hd using 1
        exact Prod.ext (by simp [hyy]) rfl
      rw [hB0, Submodule.mem_bot, Prod.snd_sub, sub_eq_zero] at h2
      exact Subtype.ext (Prod.ext hyy h2)
    have fsurj : Function.Surjective f := by
      intro v
      have hv : v ∈ Y.map (LinearMap.fst E (Fin r → E) (Fin r → E)) := hP1 ▸ Submodule.mem_top
      obtain ⟨y, hy, rfl⟩ := hv
      exact ⟨⟨y, hy⟩, rfl⟩
    let e := LinearEquiv.ofBijective f ⟨finj, fsurj⟩
    let T : (Fin r → E) →ₗ[E] (Fin r → E) :=
      (LinearMap.snd E (Fin r → E) (Fin r → E)).comp (Y.subtype.comp e.symm.toLinearMap)
    have hT : ∀ v, T v = ((e.symm v : Y) : (Fin r → E) × (Fin r → E)).2 := fun v => rfl
    have he1 : ∀ v, ((e.symm v : Y) : (Fin r → E) × (Fin r → E)).1 = v := fun v => by
      rw [← hf]
      exact e.apply_symm_apply v
    have hgraph : ∀ y : (Fin r → E) × (Fin r → E), y ∈ Y ↔ y.2 = T y.1 := by
      intro y
      constructor
      · intro hy
        have hyy : (⟨y, hy⟩ : Y) = e.symm y.1 := finj (by rw [hf, hf, he1])
        rw [hT, ← hyy]
      · intro h
        have hy : y = ((e.symm y.1 : Y) : (Fin r → E) × (Fin r → E)) :=
          Prod.ext (he1 _).symm (h.trans (hT _))
        rw [hy]
        exact (e.symm y.1).2
    set M := LinearMap.toMatrix' T with hMdef
    have hM : ∀ v, M.mulVec v = T v := fun v => LinearMap.toMatrix'_mulVec T v
    have hdet : M.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv
      have hv0 : (v, (0 : Fin r → E)) ∈ Y := by
        rw [hgraph, ← hM, hMv]
      have hvA : v ∈ A := (memA v).2 hv0
      rw [hA0, Submodule.mem_bot] at hvA
      exact hvA
    refine ⟨Matrix.nonsingInvUnit M (isUnit_iff_ne_zero.mpr hdet), ?_, ?_⟩
    · show (M.map c).transpose * J * M = J
      apply isometry_matrix
      intro x x'
      have hx := (hgraph (x, T x)).2 rfl
      have hx' := (hgraph (x', T x')).2 rfl
      have := hiso _ hx _ hx'
      rw [hM, hM]
      exact this
    · intro y
      show y ∈ Y ↔ y.2 = M.mulVec y.1
      rw [hM]
      exact hgraph y
  · rintro ⟨g, -, hg⟩
    rw [eq_bot_iff]
    intro a ha
    rw [memA, hg] at ha
    have hinv : ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
        ((g : Matrix (Fin r) (Fin r) E).mulVec a) = a := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← ha, Matrix.mulVec_zero] at hinv
    rw [Submodule.mem_bot, ← hinv]

end GlobalTheory.Doubling
