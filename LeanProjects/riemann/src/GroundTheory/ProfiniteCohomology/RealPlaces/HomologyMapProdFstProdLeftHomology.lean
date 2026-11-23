import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeMap
import GroundTheory.ProfiniteCohomology.RealPlaces.NormHomotopy
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeHomotopy
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CompactCupEqCompactCupRight
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section Pairing

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}

variable (B) in

noncomputable def tateLocalResB :
    cochainsComplex B ⟶ tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom B)
      (fun w => Rep.res (ψ w).toMonoidHom B) :=
  prodLift (localRes φ B _ fun _ => 𝟙 _) (localRes ψ B _ fun _ => 𝟙 _)

variable (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)

noncomputable def zeroCochainValue : (cochainsComplex B).X 0 →ₗ[k] B where
  toFun z := cochainOf B z (fun i => i.elim0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def tateExtraPairingAt (w : κ) : Aᵣ w →ₗ[k] (cochainsComplex B).X 0 →ₗ[k] Cᵣ w :=
  ((TensorProduct.mk k (Aᵣ w) (Rep.res (ψ w).toMonoidHom B)).compr₂ (μᵣ w).hom.toLinearMap).compl₂
    (zeroCochainValue (B := B))

noncomputable def tateExtraPairing :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X 0 →ₗ[k] (∀ w, Cᵣ w) :=
  LinearMap.mk₂ k (fun e z w => tateExtraPairingAt ψ μᵣ w (e w) z)
    (fun _ _ _ => funext fun w => LinearMap.map_add₂ (tateExtraPairingAt ψ μᵣ w) _ _ _)
    (fun _ _ _ => funext fun w => LinearMap.map_smul₂ (tateExtraPairingAt ψ μᵣ w) _ _ _)
    (fun _ _ _ => funext fun w => map_add (tateExtraPairingAt ψ μᵣ w _) _ _)
    (fun _ _ _ => funext fun w => map_smul (tateExtraPairingAt ψ μᵣ w _) _ _)

omit [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] [∀ w, IsDiscreteRep (Aᵣ w)]
  [∀ w, IsDiscreteRep (Cᵣ w)] in
theorem tateExtraPairing_apply (e : ∀ w, Aᵣ w) (z : (cochainsComplex B).X 0) (w : κ) :
    tateExtraPairing ψ μᵣ e z w = (μᵣ w).hom ((e w ⊗ₜ[k] cochainOf B z (fun i => i.elim0) :
      (Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B : Rep k (F w)))) :=
  rfl

noncomputable def tateGlobalCup :
    LeibnizPairing (tateGlobalComplex A Aᵣ) (cochainsComplex B) (tateGlobalComplex C Cᵣ) :=
  LeibnizPairing.prodLeft (cupLeibniz μ) (LeibnizPairing.degZero (tateExtraPairing ψ μᵣ))

noncomputable def tateLocalCup :
    LeibnizPairing (tateLocalComplex Aᵥ Aᵣ)
      (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom B) (fun w => Rep.res (ψ w).toMonoidHom B))
      (tateLocalComplex Cᵥ Cᵣ) :=
  LeibnizPairing.prod (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v))
    (LeibnizPairing.pi fun w => cupLeibniz (μᵣ w))

noncomputable def tateNormHomotopy {s m : ℕ} (h : s = m + 1) :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X s →ₗ[k] (∀ w, (cochainsComplex (Cᵣ w)).X m) :=
  LinearMap.mk₂ k (fun e z w => normHomotopy (μᵣ w) h (e w)
      (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f s).hom z w))
    (fun _ _ _ => funext fun w => LinearMap.map_add₂ (normHomotopy (μᵣ w) h) _ _ _)
    (fun _ _ _ => funext fun w => LinearMap.map_smul₂ (normHomotopy (μᵣ w) h) _ _ _)
    (fun e _ _ => funext fun w => by
      rw [map_add]
      exact map_add (normHomotopy (μᵣ w) h (e w)) _ _)
    (fun c e _ => funext fun w => by
      rw [map_smul]
      exact map_smul (normHomotopy (μᵣ w) h (e w)) c _)

noncomputable def tateCupHomotopyL {s m : ℕ} (h : s = m + 1) :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X s →ₗ[k] (tateLocalComplex Cᵥ Cᵣ).X m :=
  -(tateNormHomotopy ψ μᵣ h).compr₂ (LinearMap.inr k
    ((piComplex fun v => cochainsComplex (Cᵥ v)).X m) ((piComplex fun w => cochainsComplex (Cᵣ w)).X m))

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopyL_apply {s m : ℕ} (h : s = m + 1) (e : ∀ w, Aᵣ w)
    (z : (cochainsComplex B).X s) :
    tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) h e z = ((0, -tateNormHomotopy ψ μᵣ h e z) :
        (piComplex fun v => cochainsComplex (Cᵥ v)).X m ×
          (piComplex fun w => cochainsComplex (Cᵣ w)).X m) :=
  Prod.ext neg_zero rfl

noncomputable def tateCupHomotopy : ∀ (r s n : ℕ), r + s = n →
    (tateGlobalComplex A Aᵣ).X r →ₗ[k] (cochainsComplex B).X s →ₗ[k]
      shiftNegOneX (tateLocalComplex Cᵥ Cᵣ) n
  | 0, _, n + 1, h => (tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) (by omega : _ = n + 1)).comp
      (LinearMap.snd k _ ((degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X 0))
  | _, _, _, _ => 0

end Pairing

section Spec

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)
  (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
  (hμr : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (ar w) (𝟙 _) ≫ μᵣ w)

theorem normCochains_f_succ_apply' (n : ℕ) (e : (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X (n + 1)) :
    ((normCochains Aᵣ).f (n + 1)).hom e = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_succ_left (r s n : ℕ) (h : r + 1 + s = n) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) (A := A) (r + 1) s n h = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_zero_zero (s : ℕ) (h : 0 + s = 0) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) (A := A) 0 s 0 h = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_zero_succ (s n : ℕ) (h : 0 + s = n + 1) (hs : s = n + 1)
    (x : (tateGlobalComplex A Aᵣ).X 0) (z : (cochainsComplex B).X s) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) 0 s (n + 1) h x z =
      tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) hs x.2 z :=
  rfl

include hμ hμr in

theorem tateCupHomotopy_spec {r s n : ℕ} (h : r + s = n) (x : (tateGlobalComplex A Aᵣ).X r)
    (z : (cochainsComplex B).X s) :
    shiftNegOneSucc (tateLocalComplex Cᵥ Cᵣ) n (((tateCompactRes φ ψ C Cᵥ c Cᵣ cr).f n).hom
        ((tateGlobalCup ψ μ μᵣ).μ h x z)) +
        (shiftNegOneD (tateLocalComplex Cᵥ Cᵣ) n).hom (tateCupHomotopy ψ μᵣ r s n h x z) =
      shiftNegOneSucc (tateLocalComplex Cᵥ Cᵣ) n ((tateLocalCup φ ψ μᵥ μᵣ).μ h
          (((tateCompactRes φ ψ A Aᵥ a Aᵣ ar).f r).hom x) (((tateLocalResB φ ψ B).f s).hom z)) +
        tateCupHomotopy ψ μᵣ (r + 1) s (n + 1) (by omega)
          (((tateGlobalComplex A Aᵣ).d r (r + 1)).hom x) z +
        (-1 : k) ^ r • tateCupHomotopy ψ μᵣ r (s + 1) (n + 1) (by omega) x
          (((cochainsComplex B).d s (s + 1)).hom z) := by
  rcases r with _ | r
  · rcases s with _ | t
    ·
      obtain rfl : n = 0 := by omega
      rw [tateCupHomotopy_zero_zero, tateCupHomotopy_succ_left,
        tateCupHomotopy_zero_succ ψ μᵣ 1 0 _ rfl, LinearMap.zero_apply, LinearMap.zero_apply,
        LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero]
      rw [pow_zero]
      erw [one_smul]
      rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply]
      erw [tateCupHomotopyL_apply]
      refine Prod.ext ?_ ?_
      · change ((localRes φ C Cᵥ c).f 0).hom (cupPairingCochains μ h x.1 z) =
          (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f 0).hom x.1)
            (((localRes φ B _ fun _ => 𝟙 _).f 0).hom z) + 0
        rw [add_zero]
        exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
      · refine funext fun w => ?_
        change ((localRes ψ C Cᵣ cr).f 0).hom (cupPairingCochains μ h x.1 z) w +
            zeroCochain (Cᵣ w) ((Cᵣ w).ρ.norm (tateExtraPairing ψ μᵣ (show ∀ w, Aᵣ w from x.2) z w)) =
          cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w +
              zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from x.2) w)))
            (((localRes ψ B _ fun _ => 𝟙 _).f 0).hom z w) +
          -normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
            (((localRes ψ B _ fun _ => 𝟙 _).f (0 + 1)).hom (((cochainsComplex B).d 0 (0 + 1)).hom z) w)
        have hres := congrFun (localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z) w
        have hd : ((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (0 + 1)).hom
            (((cochainsComplex B).d 0 (0 + 1)).hom z) w =
            ((cochainsComplex (Rep.res (ψ w).toMonoidHom B)).d 0 (0 + 1)).hom
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f 0).hom z w) := by
          rw [hom_f_d_apply]
          exact piComplex_d_hom_apply _ 0 _ w
        have hz0 : cochainOf (Rep.res (ψ w).toMonoidHom B)
            (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f 0).hom z w)
            (fun i => i.elim0) = cochainOf B z (fun i => i.elim0) :=
          congrArg (cochainOf B z) (Subsingleton.elim _ _)
        rw [hres, LinearMap.map_add₂, hd, normHomotopy_d_zero, hz0]
        change _ + zeroCochain (Cᵣ w) ((Cᵣ w).ρ.norm ((μᵣ w).hom _)) = _
        abel
    ·
      obtain rfl : n = t + 1 := by omega
      rw [tateCupHomotopy_zero_succ ψ μᵣ (t + 1) t _ rfl, tateCupHomotopy_succ_left,
        tateCupHomotopy_zero_succ ψ μᵣ (t + 1 + 1) (t + 1) _ rfl, LinearMap.zero_apply,
        LinearMap.zero_apply, add_zero]
      rw [pow_zero]
      erw [one_smul]
      rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply, shiftNegOneD_succ_apply]
      erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply, prodComplex_d_hom_apply]
      refine Prod.ext ?_ ?_
      · change ((localRes φ C Cᵥ c).f (t + 1)).hom (cupPairingCochains μ h x.1 z) +
            -((piComplex fun v => cochainsComplex (Cᵥ v)).d t (t + 1)).hom 0 =
          (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f 0).hom x.1)
            (((localRes φ B _ fun _ => 𝟙 _).f (t + 1)).hom z) + 0
        rw [map_zero, neg_zero, add_zero, add_zero]
        exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
      · refine funext fun w => ?_
        change ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w +
            ((normCochains Cᵣ).f (t + 1)).hom
              (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) 0 (t + 1) (t + 1) h x.2 z) w +
            -(((piComplex fun w => cochainsComplex (Cᵣ w)).d t (t + 1)).hom
              (-tateNormHomotopy ψ μᵣ (rfl : t + 1 = t + 1) x.2 z) w) = _
        erw [piComplex_d_hom_apply]
        change ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w +
            ((normCochains Cᵣ).f (t + 1)).hom
              (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) 0 (t + 1) (t + 1) h x.2 z) w +
            -((cochainsComplex (Cᵣ w)).d t (t + 1)).hom
              (-normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
                (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1)).hom z w)) =
          cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w +
              zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from x.2) w)))
            (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1)).hom z w) +
          -normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
            (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1 + 1)).hom
              (((cochainsComplex B).d (t + 1) (t + 1 + 1)).hom z) w)
        have hres : ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w =
            cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w)
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (t + 1)).hom z w) :=
          congrFun (localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z) w
        have hd : ((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f
            (t + 1 + 1)).hom (((cochainsComplex B).d (t + 1) (t + 1 + 1)).hom z) w =
            ((cochainsComplex (Rep.res (ψ w).toMonoidHom B)).d (t + 1) (t + 1 + 1)).hom
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f
                (t + 1)).hom z w) := by
          rw [hom_f_d_apply]
          exact piComplex_d_hom_apply _ (t + 1) _ w
        have key := d_normHomotopy_add (μᵣ w) ((show ∀ w, Aᵣ w from x.2) w)
          (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (t + 1)).hom z w)
        rw [hres, LinearMap.map_add₂, hd, map_neg, neg_neg, ← key]
        change _ + (0 : (cochainsComplex (Cᵣ w)).X (t + 1)) + _ = _
        abel
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    rw [tateCupHomotopy_succ_left, tateCupHomotopy_succ_left, tateCupHomotopy_succ_left,
      LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero, smul_zero, add_zero,
      shiftNegOneSucc_apply, shiftNegOneSucc_apply]
    refine Prod.ext ?_ ?_
    · exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
    · change ((localRes ψ C Cᵣ cr).f (m + 1)).hom (cupPairingCochains μ h x.1 z) +
          ((normCochains Cᵣ).f (m + 1)).hom
            (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) (r + 1) s (m + 1) h x.2 z) =
        (LeibnizPairing.pi fun w => cupLeibniz (μᵣ w)).μ h
          (((localRes ψ A Aᵣ ar).f (r + 1)).hom x.1 + ((normCochains Aᵣ).f (r + 1)).hom x.2)
          (((localRes ψ B _ fun _ => 𝟙 _).f s).hom z)
      rw [normCochains_f_succ_apply', normCochains_f_succ_apply', add_zero, add_zero]
      exact localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z

end Spec

section ProdHomology

variable {M₁ M₂ N₁ N₂ P₁ P₂ N : CochainComplex (ModuleCat.{u} k) ℕ}

theorem LeibnizPairing.homologyMap_prodFst_prod_homology (μ₁ : LeibnizPairing M₁ N₁ P₁)
    (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ} (h : r + s = n)
    (x : (prodComplex M₁ M₂).homology r) (y : (prodComplex N₁ N₂).homology s) :
    (HomologicalComplex.homologyMap (prodFst P₁ P₂) n).hom ((LeibnizPairing.prod μ₁ μ₂).homology h x y) =
      μ₁.homology h ((HomologicalComplex.homologyMap (prodFst M₁ M₂) r).hom x)
        ((HomologicalComplex.homologyMap (prodFst N₁ N₂) s).hom y) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  rfl

theorem LeibnizPairing.homologyMap_prodSnd_prod_homology (μ₁ : LeibnizPairing M₁ N₁ P₁)
    (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ} (h : r + s = n)
    (x : (prodComplex M₁ M₂).homology r) (y : (prodComplex N₁ N₂).homology s) :
    (HomologicalComplex.homologyMap (prodSnd P₁ P₂) n).hom ((LeibnizPairing.prod μ₁ μ₂).homology h x y) =
      μ₂.homology h ((HomologicalComplex.homologyMap (prodSnd M₁ M₂) r).hom x)
        ((HomologicalComplex.homologyMap (prodSnd N₁ N₂) s).hom y) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  rfl

end ProdHomology

section Cup

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)
  (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
  (hμr : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (ar w) (𝟙 _) ≫ μᵣ w)

noncomputable def tateCompactCupLeibniz :
    LeibnizPairing (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar) (cochainsComplex B)
      (tateCompactCochains φ ψ C Cᵥ c Cᵣ cr) :=
  LeibnizPairing.coconeLeftHtpy (tateLocalCup φ ψ μᵥ μᵣ) (tateLocalResB φ ψ B)
    (tateGlobalCup ψ μ μᵣ) (fun {r s n} h => tateCupHomotopy ψ μᵣ r s n h)
    (fun h x z => tateCupHomotopy_spec φ ψ μ μᵥ μᵣ hμ hμr h x z)

noncomputable def tateCompactCup {r s n : ℕ} (h : r + s = n) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar r →ₗ[k] cohomology B s →ₗ[k]
      tateCompactCohomology φ ψ C Cᵥ c Cᵣ cr n :=
  (tateCompactCupLeibniz φ ψ μ μᵥ μᵣ hμ hμr).homology h

theorem tateCompactCup_tateLocalToCompact {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : (∀ v, cohomology (Aᵥ v) r) × (∀ w, cohomology (Aᵣ w) r)) (z : cohomology B s) :
    tateCompactCup φ ψ μ μᵥ μᵣ hμ hμr h' ((tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar r).hom ξ) z =
      (tateLocalToCompact φ ψ C Cᵥ c Cᵣ cr n).hom
        ((fun v => cupPairing (μᵥ v) h (ξ.1 v)
            ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) s).hom z)),
          (fun w => cupPairing (μᵣ w) h (ξ.2 w)
            ((cohomologyMapAlong (ψ w).toMonoidHom (continuous_toMonoidHom (ψ w)) (𝟙 _) s).hom z))) := by
  change (tateCompactCupLeibniz φ ψ μ μᵥ μᵣ hμ hμr).homology h'
      ((mappingCoconeNat.homologyδ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) r).hom
        ((tateLocalCohomologyIso Aᵥ Aᵣ r).inv.hom ξ)) z =
    (mappingCoconeNat.homologyδ (tateCompactRes φ ψ C Cᵥ c Cᵣ cr) n).hom
      ((tateLocalCohomologyIso Cᵥ Cᵣ n).inv.hom _)
  refine (LeibnizPairing.coconeLeftHtpy_homology_homologyδ _ _ _ _ _ h h' _ z).trans ?_
  congr 1
  apply (ModuleCat.mono_iff_injective (tateLocalCohomologyIso Cᵥ Cᵣ n).hom).1 inferInstance
  rw [hom_apply_hom_apply_of_comp_eq (tateLocalCohomologyIso Cᵥ Cᵣ n).inv_hom_id]
  have hξ := hom_apply_hom_apply_of_comp_eq (tateLocalCohomologyIso Aᵥ Aᵣ r).inv_hom_id
    (show ModuleCat.of k ((∀ v, cohomology (Aᵥ v) r) × (∀ w, cohomology (Aᵣ w) r)) from ξ)
  rw [tateLocalCohomologyIso_hom_apply] at hξ
  rw [tateLocalCohomologyIso_hom_apply]
  have ρ1 : tateLocalResB φ ψ B ≫ prodFst _ _ =
      localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) (fun _ => 𝟙 _) := prodLift_prodFst _ _
  have ρ2 : tateLocalResB φ ψ B ≫ prodSnd _ _ =
      localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) (fun _ => 𝟙 _) := prodLift_prodSnd _ _
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · rw [tateLocalCup, LeibnizPairing.homologyMap_prodFst_prod_homology]
    refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun v => cupLeibniz (μᵥ v)) h _ _ v).trans ?_
    refine (cupLeibniz_homology (μᵥ v) h _ _).trans ?_
    refine congrArg₂ (fun p q => cupPairing (μᵥ v) h p q) (congrFun (congrArg Prod.fst hξ) v) ?_
    rw [hom_apply_hom_apply_of_comp_eq
      (HomologicalComplex.homologyMap_comp (tateLocalResB φ ψ B) (prodFst _ _) s).symm z, ρ1]
    exact congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun v => cochainsMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
        (𝟙 (Rep.res (φ v).toMonoidHom B))) s) z) v
  · rw [tateLocalCup, LeibnizPairing.homologyMap_prodSnd_prod_homology]
    refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun w => cupLeibniz (μᵣ w)) h _ _ w).trans ?_
    refine (cupLeibniz_homology (μᵣ w) h _ _).trans ?_
    refine congrArg₂ (fun p q => cupPairing (μᵣ w) h p q) (congrFun (congrArg Prod.snd hξ) w) ?_
    rw [hom_apply_hom_apply_of_comp_eq
      (HomologicalComplex.homologyMap_comp (tateLocalResB φ ψ B) (prodSnd _ _) s).symm z, ρ2]
    exact congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun w => cochainsMapAlong (ψ w).toMonoidHom (continuous_toMonoidHom (ψ w))
        (𝟙 (Rep.res (ψ w).toMonoidHom B))) s) z) w

end Cup

end GroundTheory.ProfCoh
