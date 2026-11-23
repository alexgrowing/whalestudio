import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology
import GroundTheory.ProfiniteCohomology.CupProducts
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Prod

variable {k : Type u} [CommRing k]

noncomputable def prodComplex (M N : CochainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (M.X n × N.X n))
    (fun n => ModuleCat.ofHom ((M.d n (n + 1)).hom.prodMap (N.d n (n + 1)).hom))
    fun _ => ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext
      (hom_apply_hom_apply_of_comp_eq (M.d_comp_d _ _ _) x.1)
      (hom_apply_hom_apply_of_comp_eq (N.d_comp_d _ _ _) x.2))

variable (M N : CochainComplex (ModuleCat.{u} k) ℕ)

theorem prodComplex_d (n : ℕ) :
    (prodComplex M N).d n (n + 1) =
      ModuleCat.ofHom ((M.d n (n + 1)).hom.prodMap (N.d n (n + 1)).hom) := by
  unfold prodComplex
  exact CochainComplex.of_d (V := ModuleCat.{u} k) (fun n => ModuleCat.of k (M.X n × N.X n))
    (fun n => ModuleCat.ofHom ((M.d n (n + 1)).hom.prodMap (N.d n (n + 1)).hom)) n

theorem prodComplex_d_hom_apply (n : ℕ) (x : (prodComplex M N).X n) :
    ((prodComplex M N).d n (n + 1)).hom x =
      (((M.d n (n + 1)).hom x.1, (N.d n (n + 1)).hom x.2) : M.X (n + 1) × N.X (n + 1)) := by
  rw [prodComplex_d]
  rfl

theorem prodComplex_d_hom_apply' (i j : ℕ) (x : (prodComplex M N).X i) :
    ((prodComplex M N).d i j).hom x =
      (((M.d i j).hom x.1, (N.d i j).hom x.2) : M.X j × N.X j) := by
  by_cases h : i + 1 = j
  · subst h
    exact prodComplex_d_hom_apply M N i x
  · rw [(prodComplex M N).shape i j h, M.shape i j h, N.shape i j h]
    rfl

noncomputable def prodFst : prodComplex M N ⟶ M :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.fst k _ _)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (congrArg Prod.fst (prodComplex_d_hom_apply M N n x)).symm)

noncomputable def prodSnd : prodComplex M N ⟶ N :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.snd k _ _)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (congrArg Prod.snd (prodComplex_d_hom_apply M N n x)).symm)

variable {M N}

noncomputable def prodLift {P : CochainComplex (ModuleCat.{u} k) ℕ} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ prodComplex M N :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom ((f.f n).hom.prod (g.f n).hom)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => by
      change ((prodComplex M N).d n (n + 1)).hom
          (show (prodComplex M N).X n from ((f.f n).hom x, (g.f n).hom x)) =
        ((f.f (n + 1)).hom ((P.d n (n + 1)).hom x), (g.f (n + 1)).hom ((P.d n (n + 1)).hom x))
      refine (prodComplex_d_hom_apply M N n _).trans ?_
      exact Prod.ext (hom_apply_hom_apply_eq_of_comp_eq (f.comm n (n + 1)) x)
        (hom_apply_hom_apply_eq_of_comp_eq (g.comm n (n + 1)) x))

@[reassoc (attr := simp)]
theorem prodLift_prodFst {P : CochainComplex (ModuleCat.{u} k) ℕ} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodFst M N = f :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[reassoc (attr := simp)]
theorem prodLift_prodSnd {P : CochainComplex (ModuleCat.{u} k) ℕ} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodSnd M N = g :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

noncomputable def prodMapCx {M' N' : CochainComplex (ModuleCat.{u} k) ℕ} (f : M ⟶ M') (g : N ⟶ N') :
    prodComplex M N ⟶ prodComplex M' N' :=
  prodLift (prodFst M N ≫ f) (prodSnd M N ≫ g)

end Prod

section DegZero

variable {k : Type u} [CommRing k]

noncomputable def degZeroX (E : ModuleCat.{u} k) : ℕ → ModuleCat.{u} k
  | 0 => E
  | _ + 1 => ModuleCat.of k PUnit

noncomputable def degZeroComplex (E : ModuleCat.{u} k) : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (degZeroX E) (fun _ => 0) fun _ => Limits.zero_comp

theorem degZeroComplex_d (E : ModuleCat.{u} k) (i j : ℕ) : (degZeroComplex E).d i j = 0 := by
  by_cases h : i + 1 = j
  · subst h
    exact CochainComplex.of_d (V := ModuleCat.{u} k) (degZeroX E) (fun _ => 0) i
  · exact (degZeroComplex E).shape i j h

instance (E : ModuleCat.{u} k) (n : ℕ) : Subsingleton ((degZeroComplex E).X (n + 1)) :=
  inferInstanceAs (Subsingleton PUnit)

end DegZero

section Norm

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

noncomputable def zeroCochain (B : Rep.{u} k F) [IsDiscreteRep B] : B →ₗ[k] (cochainsComplex B).X 0 where
  toFun m := mkCochain B (fun _ => m) (IsLocallyConstant.const m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cochainOf_zeroCochain (B : Rep.{u} k F) [IsDiscreteRep B] (m : B) (σ : Fin 0 → F) :
    cochainOf B (zeroCochain B m) σ = m :=
  rfl

theorem cochainOf_d_zeroCochain (B : Rep.{u} k F) [IsDiscreteRep B] (m : B) (σ : Fin 1 → F) :
    cochainOf B (((cochainsComplex B).d 0 1).hom (zeroCochain B m)) σ = B.ρ (σ 0) m - m := by
  rw [cochainOf_d]
  simp [inhomogeneousCochains.d_hom_apply, cochainOf_zeroCochain, sub_eq_add_neg]

variable [Fintype F]

theorem d_zeroCochain_norm (B : Rep.{u} k F) [IsDiscreteRep B] (m : B) :
    ((cochainsComplex B).d 0 1).hom (zeroCochain B (B.ρ.norm m)) = 0 := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_d_zeroCochain, Representation.self_norm_apply, sub_self]
  rfl

end Norm

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section Norm

variable (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]

noncomputable def normCochainsF : ∀ n, (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X n ⟶
    (piComplex fun w => cochainsComplex (Aᵣ w)).X n
  | 0 => ModuleCat.ofHom (LinearMap.pi fun w =>
      (zeroCochain (Aᵣ w)).comp ((Aᵣ w).ρ.norm.comp (LinearMap.proj w)))
  | _ + 1 => 0

theorem normCochainsF_zero_apply (e : (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X 0)
    (w : κ) :
    (normCochainsF Aᵣ 0).hom e w = zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from e) w)) :=
  rfl

noncomputable def normCochains :
    degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w)) ⟶ piComplex fun w => cochainsComplex (Aᵣ w) :=
  CochainComplex.ofHom (normCochainsF Aᵣ) fun n => by
    cases n with
    | zero =>
      refine ModuleCat.hom_ext (LinearMap.ext fun e => funext fun w => ?_)
      rw [degZeroComplex_d]
      change ((piComplex fun w => cochainsComplex (Aᵣ w)).d 0 1).hom
        ((normCochainsF Aᵣ 0).hom e) w = 0
      rw [piComplex_d_hom_apply, normCochainsF_zero_apply]
      exact d_zeroCochain_norm (Aᵣ w) _
    | succ n =>
      change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
      rw [zero_comp, comp_zero]

end Norm

variable (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

noncomputable abbrev tateGlobalComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  prodComplex (cochainsComplex A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w)))

noncomputable abbrev tateLocalComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  prodComplex (piComplex fun v => cochainsComplex (Aᵥ v)) (piComplex fun w => cochainsComplex (Aᵣ w))

noncomputable def tateCompactRes : tateGlobalComplex A Aᵣ ⟶ tateLocalComplex Aᵥ Aᵣ :=
  prodLift (prodFst _ _ ≫ localRes φ A Aᵥ a)
    (prodFst _ _ ≫ localRes ψ A Aᵣ ar + prodSnd _ _ ≫ normCochains Aᵣ)

noncomputable def tateCompactCochains : CochainComplex (ModuleCat.{u} k) ℕ :=
  mappingCoconeNat (tateCompactRes φ ψ A Aᵥ a Aᵣ ar)

noncomputable def tateCompactCohomology (n : ℕ) : ModuleCat.{u} k :=
  (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar).homology n

noncomputable abbrev tateCompactCohomologyRes (n : ℕ) : ModuleCat.{u} k :=
  tateCompactCohomology φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
    (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _) n

end Tate

end GroundTheory.ProfCoh
