import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary
import Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalAutomorphicFormsUnitaryOfTypeLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupIrreducibleOfAdmissibleUnitary

private theorem UpperTheory.Reformulated.B.Gr38.matrix_comm {R₁ R₂ m : Type} [CommRing R₁] [CommRing R₂] [Fintype m]
    [DecidableEq m] (X Y : Matrix m m (R₁ × R₂))
    (hX : X.map (RingHom.snd R₁ R₂) = 1) (hY : Y.map (RingHom.fst R₁ R₂) = 1) : X * Y = Y * X := by
  have hf : (X * Y).map (RingHom.fst R₁ R₂) = (Y * X).map (RingHom.fst R₁ R₂) := by
    rw [Matrix.map_mul, Matrix.map_mul, hY, mul_one, one_mul]
  have hs : (X * Y).map (RingHom.snd R₁ R₂) = (Y * X).map (RingHom.snd R₁ R₂) := by
    rw [Matrix.map_mul, Matrix.map_mul, hX, mul_one, one_mul]
  exact Matrix.ext fun i j =>
    Prod.ext (congr_fun (congr_fun hf i) j) (congr_fun (congr_fun hs i) j)

private theorem UpperTheory.Reformulated.B.Gr38.inf_fin_comm {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {n : ℕ} (x : ↥(GlobalTheory.UnitaryBC.infU E n))
    (k : ↥(GlobalTheory.UnitaryBC.finU E n)) :
    (x : ↥(GlobalTheory.UnitaryBC.UA E n)) * (k : ↥(GlobalTheory.UnitaryBC.UA E n)) =
      (k : ↥(GlobalTheory.UnitaryBC.UA E n)) * (x : ↥(GlobalTheory.UnitaryBC.UA E n)) := by
  apply Subtype.ext
  apply Units.ext
  let X : Matrix (Fin n) (Fin n) (GlobalTheory.CuspRep.Ad E) :=
    (((x : ↥(GlobalTheory.UnitaryBC.UA E n)) : GlobalTheory.CuspRep.GA E n) : Matrix _ _ _)
  let Y : Matrix (Fin n) (Fin n) (GlobalTheory.CuspRep.Ad E) :=
    (((k : ↥(GlobalTheory.UnitaryBC.UA E n)) : GlobalTheory.CuspRep.GA E n) : Matrix _ _ _)
  have hx : X.map (GlobalTheory.CuspRep.pFin E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 x.2)
  have hk : Y.map (GlobalTheory.CuspRep.pInf E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 k.2)
  have hk' : Y.map (RingHom.fst (NumberField.InfiniteAdeleRing E) (GlobalTheory.CuspRep.Af E)) = 1 := by
    have h1 : Y.map (RingHom.fst (NumberField.InfiniteAdeleRing E) (GlobalTheory.CuspRep.Af E)) =
        (Y.map (GlobalTheory.CuspRep.pInf E)).map (GlobalTheory.CuspRep.infEq E) := by
      ext i j : 2
      exact ((GlobalTheory.CuspRep.infEq E).apply_symm_apply _).symm
    rw [h1, hk]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact UpperTheory.Reformulated.B.Gr38.matrix_comm (R₁ := NumberField.InfiniteAdeleRing E)
    (R₂ := GlobalTheory.CuspRep.Af E) X Y hx hk'

private theorem UpperTheory.Reformulated.B.Gr38.ru_comm {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {n : ℕ} (x : ↥(GlobalTheory.UnitaryBC.infU E n))
    (k : ↥(GlobalTheory.UnitaryBC.finU E n)) (φ : ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) :
    GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n)) (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ) =
      GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n)) φ) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    UpperTheory.Reformulated.B.Gr38.inf_fin_comm]

private theorem UpperTheory.Reformulated.B.Gr38.conj_fix {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V]
    (R : Representation ℂ G V) (a k : G) (φ : V) :
    R (k⁻¹ * a * k) φ = φ ↔ R a (R k φ) = R k φ := by
  have h1 : ∀ v, R k⁻¹ (R k v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have h2 : ∀ v, R k (R k⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [map_mul, map_mul]
  simp only [Module.End.mul_apply]
  constructor
  · intro h
    have := congrArg (R k) h
    rwa [h2] at this
  · intro h
    rw [h, h1]

private theorem UpperTheory.Reformulated.B.Gr38.aut_translate {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {n : ℕ} (k : ↥(GlobalTheory.UnitaryBC.finU E n))
    {φ : ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ} (h : φ ∈ GlobalTheory.DefU.autU E n) :
    GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ ∈ GlobalTheory.DefU.autU E n := by
  obtain ⟨hc, hr, ho, hf⟩ := (h : GlobalTheory.UnitaryBC.IsAutFormU φ)
  refine (GlobalTheory.UnitaryBC.IsAutFormU.mk ?_ ?_ ?_ ?_ :
    GlobalTheory.UnitaryBC.IsAutFormU (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ))
  · exact hc.comp (continuous_mul_right (k : ↥(GlobalTheory.UnitaryBC.UA E n)))
  · intro γ hγ g
    have := hr γ hγ (g * k)
    rw [← mul_assoc] at this
    exact this
  · have hs : {k' : ↥(GlobalTheory.UnitaryBC.finU E n) |
        GlobalTheory.UnitaryBC.RU E n (k' : ↥(GlobalTheory.UnitaryBC.UA E n))
          (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ) =
            GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ} =
        (fun k' : ↥(GlobalTheory.UnitaryBC.finU E n) => k⁻¹ * k' * k) ⁻¹'
          {k' : ↥(GlobalTheory.UnitaryBC.finU E n) |
            GlobalTheory.UnitaryBC.RU E n (k' : ↥(GlobalTheory.UnitaryBC.UA E n)) φ = φ} := by
      ext k'
      exact (UpperTheory.Reformulated.B.Gr38.conj_fix (GlobalTheory.UnitaryBC.RU E n) (k' : ↥(GlobalTheory.UnitaryBC.UA E n))
        (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ).symm
    rw [hs]
    exact ho.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have hs : Submodule.span ℂ (Set.range fun x : ↥(GlobalTheory.UnitaryBC.infU E n) =>
        GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n))
          (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ)) =
        (Submodule.span ℂ (Set.range fun x : ↥(GlobalTheory.UnitaryBC.infU E n) =>
          GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n)) φ)).map
            (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext x
      exact UpperTheory.Reformulated.B.Gr38.ru_comm x k φ
    rw [hs]
    infer_instance

private def UpperTheory.Reformulated.B.Gr38.fixer {G W : Type} [Group G] [AddCommGroup W] [_root_.Module ℂ W]
    (R : Representation ℂ G W) (w : W) : Subgroup G where
  carrier := {g | R g w = w}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h : R a⁻¹ (R a w) = w := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    rwa [ha] at h

private theorem UpperTheory.Reformulated.B.Gr38.orbit_finite {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [_root_.Module ℂ W] (R : Representation ℂ G W)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (w : W)
    (hw : IsOpen (UpperTheory.Reformulated.B.Gr38.fixer R w : Set G)) :
    (Set.range fun k : ↥K => R (k : G) w).Finite := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let U : Subgroup ↥K := (UpperTheory.Reformulated.B.Gr38.fixer R w).subgroupOf K
  have hU : IsOpen (U : Set ↥K) := hw.preimage continuous_subtype_val
  haveI : Finite (↥K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  refine (Set.finite_range (fun c : ↥K ⧸ U => R ((c.out : ↥K) : G) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U k
  refine ⟨(k : ↥K ⧸ U), ?_⟩
  have hfix : R ((h : ↥K) : G) w = w := h.2
  simp only [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hfix]

private theorem UpperTheory.Reformulated.B.Gr38.stab_open {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S] [_root_.Module ℂ S]
    [FiniteDimensional ℂ S] (f : S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
    (hf : ∀ v, f v ∈ GlobalTheory.DefU.autU E n) :
    IsOpen {k : ↥(GlobalTheory.UnitaryBC.finU E n) |
      ∀ v, GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (f v) = f v} := by
  let b := Module.finBasis ℂ S
  have hs : {k : ↥(GlobalTheory.UnitaryBC.finU E n) |
      ∀ v, GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (f v) = f v} =
      ⋂ i, {k : ↥(GlobalTheory.UnitaryBC.finU E n) |
        GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (f (b i)) = f (b i)} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h i => h _, fun h v => ?_⟩
    have : (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n))) ∘ₗ f = f := b.ext h
    exact LinearMap.congr_fun this v
  rw [hs]
  refine isOpen_iInter_of_finite fun i => ?_
  obtain ⟨_, _, ho, _⟩ := (hf (b i) : GlobalTheory.UnitaryBC.IsAutFormU (f (b i)))
  exact ho

noncomputable def UpperTheory.Reformulated.B.Gr38.eqForms :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          [inst_2 : NumberField.IsCMField E] →
            {n : ℕ} →
              {S : Type} →
                [inst_3 : AddCommGroup S] →
                  [inst_4 : _root_.Module ℂ S] →
                    Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S → Submodule ℂ (S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) :=
    fun {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S]
        [_root_.Module ℂ S] (ρ : Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S) ↦
      {
        carrier :=
          {f : S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ |
            (∀ (v : S), (f : S → ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) v ∈ GlobalTheory.DefU.autU E n) ∧
              ∀ (x : ↥(GlobalTheory.UnitaryBC.infU E n)) (v : S),
                (f : S → ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) (((ρ : ↥(GlobalTheory.UnitaryBC.infU E n) → S →ₗ[ℂ] S) x : S → S) v) =
                  ((GlobalTheory.UnitaryBC.RU E n :
                                   ↥(GlobalTheory.UnitaryBC.UA E n) → (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
                                 (↑x : ↥(GlobalTheory.UnitaryBC.UA E n)) :
                      (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) → ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
                    ((f : S → ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) v)},
        add_mem' := (by
          intro f g hf hg
          refine ⟨fun v => (GlobalTheory.DefU.autU E n).add_mem (hf.1 v) (hg.1 v), fun x v => ?_⟩
          simp only [LinearMap.add_apply, hf.2 x v, hg.2 x v, map_add]),
        zero_mem' := (by
          refine ⟨fun v => (GlobalTheory.DefU.autU E n).zero_mem, fun x v => ?_⟩
          simp only [LinearMap.zero_apply, map_zero]),
        smul_mem' := (by
          intro c f hf
          refine ⟨fun v => (GlobalTheory.DefU.autU E n).smul_mem c (hf.1 v), fun x v => ?_⟩
          simp only [LinearMap.smul_apply, hf.2 x v, map_smul]) : Submodule ℂ (S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) }

noncomputable def UpperTheory.Reformulated.B.Gr38.eqRep :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          [inst_2 : NumberField.IsCMField E] →
            {n : ℕ} →
              {S : Type} →
                [inst_3 : AddCommGroup S] →
                  [inst_4 : _root_.Module ℂ S] →
                    (ρ : Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S) →
                      Representation ℂ ↥(GlobalTheory.UnitaryBC.finU E n) ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) :=
    fun {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S]
        [_root_.Module ℂ S] (ρ : Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S) ↦
      {
        toFun := fun (k : ↥(GlobalTheory.UnitaryBC.finU E n)) ↦
          ((LinearMap.llcomp ℂ S (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) :
                  ((↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →
                    (S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →ₗ[ℂ] S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
                ((GlobalTheory.UnitaryBC.RU E n :
                    ↥(GlobalTheory.UnitaryBC.UA E n) → (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
                  (↑k : ↥(GlobalTheory.UnitaryBC.UA E n)))).restrict
            (by
              intro g hg
              refine ⟨fun v => UpperTheory.Reformulated.B.Gr38.aut_translate k (hg.1 v), fun x v => ?_⟩
              show GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (g (ρ x v)) =
                GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n))
                  (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (g v))
              rw [hg.2 x v, UpperTheory.Reformulated.B.Gr38.ru_comm]),
        map_one' := (by
          apply LinearMap.ext
          intro g
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          show GlobalTheory.UnitaryBC.RU E n ((1 : ↥(GlobalTheory.UnitaryBC.finU E n)) : ↥(GlobalTheory.UnitaryBC.UA E n)) (g.1 v) = g.1 v
          simp),
        map_mul' := (by
          intro k l
          apply LinearMap.ext
          intro g
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          show GlobalTheory.UnitaryBC.RU E n ((k * l : ↥(GlobalTheory.UnitaryBC.finU E n)) : ↥(GlobalTheory.UnitaryBC.UA E n)) (g.1 v) =
            GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n))
              (GlobalTheory.UnitaryBC.RU E n (l : ↥(GlobalTheory.UnitaryBC.UA E n)) (g.1 v))
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]) :
        ↥(GlobalTheory.UnitaryBC.finU E n) →* ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) →ₗ[ℂ] ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) }

theorem UpperTheory.Reformulated.B.Gr38.eqRep_adm :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {n : ℕ} {S : Type}
      [inst_3 : AddCommGroup S] [inst_4 : _root_.Module ℂ S] [FiniteDimensional ℂ S]
      (ρ : Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S) (f : ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ)),
      ∃ (K : Subgroup ↥(GlobalTheory.UnitaryBC.finU E n)),
        (∀ k ∈ K,
            ((UpperTheory.Reformulated.B.Gr38.eqRep ρ :
                            ↥(GlobalTheory.UnitaryBC.finU E n) → ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) →ₗ[ℂ] ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ))
                          k :
                  ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) → ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ))
                f =
              f) ∧
          FiniteDimensional ℂ ↥(GlobalTheory.PRep.fixed (UpperTheory.Reformulated.B.Gr38.eqRep ρ) K) ∧
            ∀ (w : ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ)),
              (Set.range fun (k : ↥K) ↦
                  ((UpperTheory.Reformulated.B.Gr38.eqRep ρ :
                                ↥(GlobalTheory.UnitaryBC.finU E n) → ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) →ₗ[ℂ] ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ))
                        (↑k : ↥(GlobalTheory.UnitaryBC.finU E n)) :
                      ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) → ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ))
                    w).Finite := by
  intro E _ _ _ n S _ _ _ ρ f
  obtain ⟨K0, hK0o, hK0c⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E n
  have hopen : ∀ w : ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ),
      IsOpen (UpperTheory.Reformulated.B.Gr38.fixer (UpperTheory.Reformulated.B.Gr38.eqRep ρ) w : Set ↥(GlobalTheory.UnitaryBC.finU E n)) := by
    intro w
    have hs : (UpperTheory.Reformulated.B.Gr38.fixer (UpperTheory.Reformulated.B.Gr38.eqRep ρ) w : Set ↥(GlobalTheory.UnitaryBC.finU E n)) =
        {k : ↥(GlobalTheory.UnitaryBC.finU E n) |
          ∀ v, GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (w.1 v) = w.1 v} := by
      ext k
      constructor
      · intro h v
        exact LinearMap.congr_fun (congrArg Subtype.val (show UpperTheory.Reformulated.B.Gr38.eqRep ρ k w = w from h)) v
      · intro h
        show UpperTheory.Reformulated.B.Gr38.eqRep ρ k w = w
        exact Subtype.ext (LinearMap.ext h)
    rw [hs]
    exact UpperTheory.Reformulated.B.Gr38.stab_open w.1 w.2.1
  let K : Subgroup ↥(GlobalTheory.UnitaryBC.finU E n) :=
    K0 ⊓ UpperTheory.Reformulated.B.Gr38.fixer (UpperTheory.Reformulated.B.Gr38.eqRep ρ) f
  have hKo : IsOpen (K : Set ↥(GlobalTheory.UnitaryBC.finU E n)) := hK0o.inter (hopen f)
  have hKc : IsCompact (K : Set ↥(GlobalTheory.UnitaryBC.finU E n)) :=
    hK0c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) Set.inter_subset_left
  refine ⟨K, fun k hk => hk.2, ?_, fun w =>
    UpperTheory.Reformulated.B.Gr38.orbit_finite (UpperTheory.Reformulated.B.Gr38.eqRep ρ) K hKc w (hopen w)⟩
  let M : Submodule ℂ (S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) :=
    (GlobalTheory.PRep.fixed (UpperTheory.Reformulated.B.Gr38.eqRep ρ) K).map (UpperTheory.Reformulated.B.Gr38.eqForms ρ).subtype
  have hM : FiniteDimensional ℂ ↥M := by
    refine UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level E n S (fun x => ρ x) K hKo M ?_
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨fun v γ hγ g => ?_, fun x v => w.2.2 x v, fun k hk v => ?_⟩
    · obtain ⟨_, hr, _, _⟩ := (w.2.1 v : GlobalTheory.UnitaryBC.IsAutFormU (w.1 v))
      exact hr γ hγ g
    · have h1 : UpperTheory.Reformulated.B.Gr38.eqRep ρ k w = w := by
        have := hw ⟨k, hk⟩
        simpa using this
      exact LinearMap.congr_fun (congrArg Subtype.val h1) v
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective (UpperTheory.Reformulated.B.Gr38.eqForms ρ).subtype
      (Submodule.injective_subtype _) (GlobalTheory.PRep.fixed (UpperTheory.Reformulated.B.Gr38.eqRep ρ) K)).symm
