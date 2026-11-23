import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct

noncomputable section

namespace GlobalTheory.IndLineGL

open GlobalTheory.SmGL GlobalTheory.PRep
open scoped TensorProduct

section MidColumn

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [LinearOrder ι] {m : ℕ}
  {c : Fin 3 → ι → Type} [∀ j i, Fintype (c j i)] [∀ j i, DecidableEq (c j i)]
  {X : Type} [AddCommGroup X] [Module ℂ X]

theorem midCol_mem_parab (g : ∀ j, (Σ i, c j i) ≃ Fin (blk3 m j)) {j : Fin 3} (hj : j ≠ 1)
    (y : GL (Fin (blk3 m j)) k) : y ∈ parab k (g j) := by
  have hs : blk3 m j ≤ 1 := by
    rcases j with ⟨_ | _ | _ | n, hn⟩
    · exact Nat.le_of_eq rfl
    · exact absurd (Fin.ext rfl) hj
    · exact Nat.le_of_eq rfl
    · omega
  haveI : Subsingleton (Fin (blk3 m j)) := Fin.subsingleton_iff_le_one.2 hs
  refine mem_parab.2 fun i i' h => ?_
  rw [Subsingleton.elim i i'] at h
  exact absurd h (lt_irrefl _)

variable (k m) in

def midColDrop : Levi k (fun j : Fin 3 => Fin (blk3 m j)) →* Levi k (fun j : Fin 3 => Fin (blk3 m j)) where
  toFun x := Function.update x 1 1
  map_one' := by simp
  map_mul' x y := by rw [← Function.update_mul, one_mul]

theorem midColDrop_mem (g : ∀ j, (Σ i, c j i) ≃ Fin (blk3 m j)) (x : Levi k (fun j : Fin 3 => Fin (blk3 m j))) :
    midColDrop k m x ∈ relParab k g := by
  refine (Subgroup.mem_pi _).2 fun j _ => ?_
  rcases eq_or_ne j 1 with rfl | hj
  · show Function.update x 1 1 1 ∈ parab k (g 1)
    rw [Function.update_self]
    exact one_mem _
  · exact midCol_mem_parab g hj _

theorem midIncl_apply_one (h : GL (Fin (blk3 m 1)) k) : midIncl k m h 1 = h :=
  Pi.mulSingle_eq_same (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) 1 h

theorem midIncl_apply_of_ne {j : Fin 3} (hj : j ≠ 1) (h : GL (Fin (blk3 m 1)) k) : midIncl k m h j = 1 :=
  Pi.mulSingle_eq_of_ne (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) hj h

theorem continuous_midIncl : Continuous (midIncl k m) := by
  refine continuous_pi fun j => ?_
  rcases eq_or_ne j 1 with rfl | hj
  · exact continuous_id.congr fun a => (midIncl_apply_one a).symm
  · exact continuous_const.congr fun a => (midIncl_apply_of_ne hj a).symm

theorem midIncl_mem_relParab (g : ∀ j, (Σ i, c j i) ≃ Fin (blk3 m j)) (p : parab k (g 1)) :
    midIncl k m p.1 ∈ relParab k g := by
  refine (Subgroup.mem_pi _).2 fun j _ => ?_
  rcases eq_or_ne j 1 with rfl | hj
  · rw [midIncl_apply_one]
    exact p.2
  · rw [midIncl_apply_of_ne hj]
    exact one_mem _

variable (g : ∀ j, (Σ i, c j i) ≃ Fin (blk3 m j)) (ρ : Representation ℂ (∀ j, Levi k (c j)) X)

abbrev midColSrc : Representation ℂ (relParab k g) X := (twist ρ (relDeltaHalf k c)).comp (relProj k g)

theorem relProj_midIncl (p : parab k (g 1)) :
    relProj k g ⟨midIncl k m p.1, midIncl_mem_relParab g p⟩ =
      Pi.mulSingle 1 (leviProj k (g 1) p) := by
  funext j
  rcases eq_or_ne j 1 with rfl | hj
  · rw [Pi.mulSingle_eq_same]
    exact congrArg (leviProj k (g 1)) (Subtype.ext (midIncl_apply_one p.1))
  · rw [Pi.mulSingle_eq_of_ne hj]
    exact (congrArg (leviProj k (g j)) (Subtype.ext (midIncl_apply_of_ne hj p.1))).trans
      (map_one _)

theorem midColSrc_midIncl (p : parab k (g 1)) :
    midColSrc g ρ ⟨midIncl k m p.1, midIncl_mem_relParab g p⟩ =
      (twist (ρ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) 1)) (deltaHalf k (c 1))).comp
        (leviProj k (g 1)) p := by
  refine LinearMap.ext fun v => ?_
  simp only [midColSrc, MonoidHom.coe_comp, Function.comp_apply, twist_apply, relProj_midIncl,
    MonoidHom.mulSingle_apply, relDeltaHalf_apply]
  rw [Finset.prod_eq_single (1 : Fin 3) (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one])
    (by simp), Pi.mulSingle_eq_same]

def midColRes (F : smoothPart (ind (relParab k g) (midColSrc g ρ))) :
    IndSp (g 1) (ρ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) 1)) :=
  ⟨⟨fun h => F.1.1 (midIncl k m h), fun p h => by
      exact (congrArg F.1.1 (map_mul (midIncl k m) p.1 h)).trans <| (F.1.2 ⟨_, midIncl_mem_relParab g p⟩ (midIncl k m h)).trans
        (LinearMap.congr_fun (midColSrc_midIncl g ρ p) _)⟩,
    by
      have hF : IsOpen {z : Levi k (fun j : Fin 3 => Fin (blk3 m j)) |
          ind (relParab k g) (midColSrc g ρ) z F.1 = F.1} := F.2
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hF.preimage continuous_midIncl).mem_nhds
        (by show ind (relParab k g) (midColSrc g ρ) (midIncl k m 1) F.1 = F.1; rw [map_one, map_one]; rfl)) fun h hh => ?_)
      apply Subtype.ext
      funext x
      exact (congrArg F.1.1 (map_mul (midIncl k m) x h)).trans (congrFun (congrArg Subtype.val hh) _)⟩

variable {g ρ} in

def midColExt (hZ : {z : Levi k (fun j : Fin 3 => Fin (blk3 m j)) |
      ∀ w : X, midColSrc g ρ ⟨midColDrop k m z, midColDrop_mem g z⟩ w = w} ∈ nhds 1)
    (φ : IndSp (g 1) (ρ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) 1))) :
    smoothPart (ind (relParab k g) (midColSrc g ρ)) :=
  ⟨⟨fun x => midColSrc g ρ ⟨midColDrop k m x, midColDrop_mem g x⟩ (φ.1.1 (x 1)), fun q x => by
      have key : (⟨midColDrop k m (q.1 * x), midColDrop_mem g _⟩ : relParab k g) *
          ⟨midIncl k m (q.1 1), midIncl_mem_relParab g ⟨q.1 1, q.2 1 trivial⟩⟩ =
          q * ⟨midColDrop k m x, midColDrop_mem g x⟩ := by
        apply Subtype.ext
        funext j
        rcases eq_or_ne j 1 with rfl | hj
        · show Function.update (q.1 * x) 1 1 1 * midIncl k m (q.1 1) 1 = q.1 1 * Function.update x 1 1 1
          rw [Function.update_self, Function.update_self, midIncl_apply_one, one_mul, mul_one]
        · show Function.update (q.1 * x) 1 1 j * midIncl k m (q.1 1) j = q.1 j * Function.update x 1 1 j
          rw [Function.update_of_ne hj, Function.update_of_ne hj, midIncl_apply_of_ne hj, mul_one, Pi.mul_apply]
      have h1 : φ.1.1 (q.1 1 * x 1) = midColSrc g ρ ⟨midIncl k m (q.1 1),
          midIncl_mem_relParab g ⟨q.1 1, q.2 1 trivial⟩⟩ (φ.1.1 (x 1)) :=
        (φ.1.2 ⟨q.1 1, q.2 1 trivial⟩ (x 1)).trans
          (LinearMap.congr_fun (midColSrc_midIncl g ρ ⟨q.1 1, q.2 1 trivial⟩) _).symm
      show midColSrc g ρ ⟨midColDrop k m (q.1 * x), midColDrop_mem g _⟩ (φ.1.1 (q.1 1 * x 1)) =
        midColSrc g ρ q (midColSrc g ρ ⟨midColDrop k m x, midColDrop_mem g x⟩ (φ.1.1 (x 1)))
      calc _ = midColSrc g ρ ((⟨midColDrop k m (q.1 * x), midColDrop_mem g _⟩ : relParab k g) *
            ⟨midIncl k m (q.1 1), midIncl_mem_relParab g ⟨q.1 1, q.2 1 trivial⟩⟩) (φ.1.1 (x 1)) := by
            rw [h1, map_mul (midColSrc g ρ)]; rfl
        _ = _ := by rw [key, map_mul (midColSrc g ρ)]; rfl⟩,
    by
      have hφ : IsOpen {h : GL (Fin (blk3 m 1)) k | ind (parab k (g 1))
          ((twist (ρ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) 1)) (deltaHalf k (c 1))).comp
            (leviProj k (g 1))) h φ.1 = φ.1} := φ.2
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem
        ((hφ.preimage (continuous_apply 1)).mem_nhds
          (by show ind (parab k (g 1)) _ 1 φ.1 = φ.1; rw [map_one]; rfl)) hZ) fun z hz => ?_)
      obtain ⟨h1, h2⟩ := hz
      simp only [Set.mem_setOf_eq, Set.mem_preimage] at h1 h2
      apply Subtype.ext
      funext x
      have e1 : φ.1.1 (x 1 * z 1) = φ.1.1 (x 1) := congrFun (congrArg Subtype.val h1) (x 1)
      have e2 : (⟨midColDrop k m (x * z), midColDrop_mem g _⟩ : relParab k g) =
          ⟨midColDrop k m x, midColDrop_mem g x⟩ * ⟨midColDrop k m z, midColDrop_mem g z⟩ :=
        Subtype.ext (map_mul _ _ _)
      show midColSrc g ρ ⟨midColDrop k m (x * z), midColDrop_mem g _⟩ (φ.1.1 (x 1 * z 1)) =
        midColSrc g ρ ⟨midColDrop k m x, midColDrop_mem g x⟩ (φ.1.1 (x 1))
      rw [e1, e2, map_mul, Module.End.mul_apply, h2]⟩

variable {g ρ} in

theorem nonempty_midCol_equiv (hZ : {z : Levi k (fun j : Fin 3 => Fin (blk3 m j)) |
      ∀ w : X, midColSrc g ρ ⟨midColDrop k m z, midColDrop_mem g z⟩ w = w} ∈ nhds 1) :
    Nonempty (Representation.Equiv ((relInd g ρ).comp (midIncl k m))
      (parInd (g 1) (ρ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) 1)))) := by
  refine ⟨Representation.Equiv.mk' ⟨⟨⟨midColRes g ρ, fun F G => Subtype.ext (Subtype.ext rfl)⟩,
    fun t F => Subtype.ext (Subtype.ext rfl)⟩, fun h => ?_⟩ (midColExt hZ) (fun F => ?_) (fun φ => ?_)⟩
  · refine LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact (congrArg F.1.1 (map_mul (midIncl k m) x h)).symm
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show midColSrc g ρ ⟨midColDrop k m x, midColDrop_mem g x⟩ (F.1.1 (midIncl k m (x 1))) = F.1.1 x
    rw [← F.1.2 ⟨midColDrop k m x, midColDrop_mem g x⟩ (midIncl k m (x 1))]
    refine congrArg F.1.1 ?_
    funext j
    rcases eq_or_ne j 1 with rfl | hj
    · show Function.update x 1 1 1 * midIncl k m (x 1) 1 = x 1
      rw [Function.update_self, midIncl_apply_one, one_mul]
    · show Function.update x 1 1 j * midIncl k m (x 1) j = x j
      rw [Function.update_of_ne hj, midIncl_apply_of_ne hj, mul_one]
  · refine Subtype.ext (Subtype.ext (funext fun h => ?_))
    show midColSrc g ρ ⟨midColDrop k m (midIncl k m h), midColDrop_mem g _⟩ (φ.1.1 (midIncl k m h 1)) = φ.1.1 h
    have e : (⟨midColDrop k m (midIncl k m h), midColDrop_mem g _⟩ : relParab k g) = 1 := by
      apply Subtype.ext
      funext j
      rcases eq_or_ne j 1 with rfl | hj
      · exact Function.update_self (1 : Fin 3) (1 : GL (Fin (blk3 m 1)) k) (midIncl k m h)
      · simp [midColDrop, midIncl_apply_of_ne hj, Function.update_of_ne hj]
    rw [e, map_one, Module.End.one_apply, midIncl_apply_one]

theorem continuous_relProj_midCol : Continuous (relProj k g) :=
  continuous_pi fun j => (ProdIrr.continuous_leviProj (g j)).comp
    (((continuous_apply j).comp continuous_subtype_val).subtype_mk fun p : relParab k g => p.2 j trivial)

theorem midCol_nhds (hρ : IsSmooth ρ) (w₀ : X) (hw : ∀ w : X, ∃ t : ℂ, w = t • w₀)
    (hδ : IsSmoothChar (relDeltaHalf k c)) :
    {z : Levi k (fun j : Fin 3 => Fin (blk3 m j)) |
      ∀ w : X, midColSrc g ρ ⟨midColDrop k m z, midColDrop_mem g z⟩ w = w} ∈ nhds 1 := by
  let d : Levi k (fun j : Fin 3 => Fin (blk3 m j)) →* relParab k g :=
    (midColDrop k m).codRestrict _ (midColDrop_mem g)
  have hd : Continuous d := (continuous_id.update 1 continuous_const).subtype_mk (midColDrop_mem g)
  have hs : IsSmooth ((midColSrc g ρ).comp d) :=
    isSmooth_comp (isSmooth_comp (isSmooth_twist hρ hδ) _ (continuous_relProj_midCol g)) _ hd
  refine Filter.mem_of_superset ((hs w₀).mem_nhds (by simp)) fun z hz w => ?_
  obtain ⟨t, rfl⟩ := hw w
  rw [map_smul]
  exact congrArg (t • ·) hz

end MidColumn

section Det

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_relDeltaHalf {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
    (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] :
    IsSmoothChar (relDeltaHalf k c) := by
  unfold relDeltaHalf
  refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun i _ => ?_
  · unfold IsSmoothChar; simp
  · exact (isSmoothChar_deltaHalf k).comp _ (continuous_apply i)

theorem isSmooth_relJac_swap {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
    {mr : α → Type} [∀ i, Fintype (mr i)] [∀ i, DecidableEq (mr i)]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    {W : Type} [AddCommGroup W] [Module ℂ W] (f : ∀ i, (Σ j, c i j) ≃ mr i)
    {ρ : Representation ℂ (Levi k mr) W} (hρ : IsSmooth ρ) :
    IsSmooth ((relJac f ρ).comp (swapBlocks k c)) :=
  isSmooth_comp (isSmooth_twist (isSmooth_jacquet hρ _ _ _
      (continuous_pi fun i => (continuous_leviEmb k (f i)).comp (continuous_apply i)))
    (isSmoothChar_relDeltaHalf c).inv) _
    (continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j))

theorem jacquet_detPair_eq_smul (a a' : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (N : Subgroup (Levi k (Two (Fin a) (Fin a'))))
    (w : Jacquet (detPair k a a' α₀ β₀) N) :
    ∃ t : ℂ, w = t • Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have key : v = TensorProduct.lid ℂ ℂ v • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) :=
    (TensorProduct.lid ℂ ℂ).injective (by rw [map_smul, TensorProduct.lid_tmul]; simp)
  exact ⟨TensorProduct.lid ℂ ℂ v, by rw [← Submodule.Quotient.mk_smul, ← key]⟩

end Det

theorem nonempty_cell_midIncl_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    ∀ (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j)),
    Nonempty (Representation.Equiv ((cellFunctor f g (detPair k a a' α₀ β₀)).comp (midIncl k m))
      (parInd (g 1) (colRep f (detPair k a a' α₀ β₀) 1))) := by
  intro k _ _ _ _ a a' m α₀ β₀ hα hβ b f g
  exact nonempty_midCol_equiv (c := fun j i => Fin (b.1 i j)) (g := g)
    (ρ := (relJac f (detPair k a a' α₀ β₀)).comp (swapBlocks k _))
    (midCol_nhds g _ (isSmooth_relJac_swap f (isSmooth_detPair a a' hα hβ)) _
      (jacquet_detPair_eq_smul a a' α₀ β₀ _) (isSmoothChar_relDeltaHalf _))

end GlobalTheory.IndLineGL
