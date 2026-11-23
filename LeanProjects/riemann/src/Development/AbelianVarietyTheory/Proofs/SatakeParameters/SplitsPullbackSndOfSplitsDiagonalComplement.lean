import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry

noncomputable section
namespace GlobalTheory.EtC.Tr

theorem splits_pullbackSnd_of_splits_diagComplHom {Z X V : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f]
    (v : V ⟶ Z) (h : Splits (diagComplHom f) v) : Splits (pullback.snd f f) v := by
  obtain ⟨m, s, hs, hiso⟩ := h
  have hδs : pullback.diagonal f ≫ pullback.snd f f = 𝟙 Z := pullback.diagonal_snd f
  let t : Fin (m + 1) → (V ⟶ pullback f f) :=
    Fin.cons (α := fun _ => V ⟶ pullback f f) (v ≫ pullback.diagonal f) (fun j => s j ≫ (diagCompl f).ι)
  have ht0 : t 0 = v ≫ pullback.diagonal f := rfl
  have hts : ∀ k : Fin m, t k.succ = s k ≫ (diagCompl f).ι := fun k => rfl
  have ht : ∀ j, t j ≫ pullback.snd f f = v := by
    intro j
    induction j using Fin.cases with
    | zero => rw [ht0, Category.assoc, hδs, Category.comp_id]
    | succ k => rw [hts, Category.assoc]; exact hs k
  refine ⟨m + 1, t, ht, ?_⟩
  let d : Fin m → (V ⟶ pullback (diagComplHom f) v) :=
    fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])
  let Φ : ∐ (fun _ : Fin m => V) ⟶ pullback (diagComplHom f) v := Sigma.desc d
  have hΦ : IsIso Φ := hiso
  have hdΦ : ∀ k, d k = Sigma.ι (fun _ : Fin m => V) k ≫ Φ := fun k => (Sigma.ι_desc _ _).symm
  let eU : pullback (diagComplHom f) v ⟶ pullback (pullback.snd f f) v :=
    pullback.map (diagComplHom f) v (pullback.snd f f) v (diagCompl f).ι (𝟙 V) (𝟙 Z)
      (by simp [diagComplHom]) (by simp)
  let eD : pullback (pullback.diagonal f ≫ pullback.snd f f) v ⟶ pullback (pullback.snd f f) v :=
    pullback.map _ v (pullback.snd f f) v (pullback.diagonal f) (𝟙 V) (𝟙 Z) (by simp) (by simp)
  let l : V ⟶ pullback (pullback.diagonal f ≫ pullback.snd f f) v :=
    pullback.lift v (𝟙 V) (by rw [hδs]; simp)
  have hl : IsIso l := by
    have h1 : IsIso (pullback.diagonal f ≫ pullback.snd f f) := by rw [hδs]; infer_instance
    have h2 : l ≫ pullback.snd _ _ = 𝟙 V := pullback.lift_snd _ _ _
    have h3 : IsIso (l ≫ pullback.snd (pullback.diagonal f ≫ pullback.snd f f) v) := by
      rw [h2]; infer_instance
    exact IsIso.of_isIso_comp_right l (pullback.snd _ _)
  let g : Fin (m + 1) → (V ⟶ pullback (pullback.snd f f) v) :=
    Fin.cons (α := fun _ => V ⟶ pullback (pullback.snd f f) v) (l ≫ eD) (fun k => d k ≫ eU)
  have hg : (Sigma.desc (fun j => pullback.lift (t j) (𝟙 V) (by rw [ht j, Category.id_comp])) :
      ∐ (fun _ : Fin (m + 1) => V) ⟶ pullback (pullback.snd f f) v) = Sigma.desc g := by
    refine Sigma.hom_ext _ _ (fun j => ?_)
    rw [Sigma.ι_desc, Sigma.ι_desc]
    induction j using Fin.cases with
    | zero =>
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show t 0 = (l ≫ eD) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ht0]
      · rw [pullback.lift_snd]
        show 𝟙 V = (l ≫ eD) ≫ _
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
    | succ k =>
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show t k.succ = (d k ≫ eU) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hts]
      · rw [pullback.lift_snd]
        show 𝟙 V = (d k ≫ eU) ≫ _
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  rw [hg]
  have hΦi : IsOpenImmersion Φ := inferInstance
  have hι : ∀ k, IsOpenImmersion (Sigma.ι (fun _ : Fin m => V) k) := fun k => inferInstance
  have hδo : IsOpenImmersion (pullback.diagonal f) := inferInstance
  have hUo : IsOpenImmersion eU := inferInstance
  have hDo : IsOpenImmersion eD := inferInstance
  have hgo : ∀ j, IsOpenImmersion (g j) := by
    intro j
    induction j using Fin.cases with
    | zero => show IsOpenImmersion (l ≫ eD); infer_instance
    | succ k => show IsOpenImmersion (d k ≫ eU); rw [hdΦ]; infer_instance
  have hgπ' : ∀ j, g j ≫ pullback.fst (pullback.snd f f) v = t j := by
    intro j
    induction j using Fin.cases with
    | zero =>
      show (l ≫ eD) ≫ _ = t 0
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ht0]
    | succ k =>
      show (d k ≫ eU) ≫ _ = t k.succ
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hts]
  have hgπ : ∀ j y, pullback.fst (pullback.snd f f) v (g j y) = t j y := by
    intro j y
    rw [← Scheme.Hom.comp_apply, hgπ']
  have hsep : ∀ a b, pullback.diagonal f a ≠ (diagCompl f).ι b := by
    intro a b hab
    have hb : (diagCompl f).ι b ∈ Set.range (diagCompl f).ι := ⟨b, rfl⟩
    rw [Scheme.Opens.range_ι] at hb
    exact hb ⟨a, hab⟩
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨isOpenImmersion_sigmaDesc _ g ?_, ⟨fun p => ?_⟩⟩
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have hπ := congrArg (pullback.fst (pullback.snd f f) v) hy
    rw [hgπ, hgπ] at hπ
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact hij rfl
      | succ k =>
        rw [ht0, hts, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hπ
        exact hsep _ _ hπ.symm
    | succ k =>
      induction j using Fin.cases with
      | zero =>
        rw [ht0, hts, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hπ
        exact hsep _ _ hπ
      | succ k' =>
        have h1 : d k' y = d k x := by
          apply eU.isOpenEmbedding.injective
          have hy' : (d k' ≫ eU) y = (d k ≫ eU) x := hy
          rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hy'
        rw [hdΦ, hdΦ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
        have h2 := (sigmaι_eq_iff _ _ _ _ _).mp (Φ.isOpenEmbedding.injective h1)
        exact hij (by rw [(Sigma.mk.inj_iff.mp h2).1])
  · by_cases hp : pullback.fst (pullback.snd f f) v p ∈ Set.range (pullback.diagonal f)
    · have hpD : p ∈ Set.range eD := by
        rw [Scheme.Pullback.range_map]
        exact ⟨hp, ⟨pullback.snd (pullback.snd f f) v p, rfl⟩⟩
      obtain ⟨q, rfl⟩ := hpD
      refine ⟨Sigma.ι (fun _ : Fin (m + 1) => V) 0 (inv l q), ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      show (l ≫ eD) (inv l q) = eD q
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (inv l), IsIso.inv_hom_id]
      rfl
    · have hpU : p ∈ Set.range eU := by
        rw [Scheme.Pullback.range_map]
        refine ⟨?_, ⟨pullback.snd (pullback.snd f f) v p, rfl⟩⟩
        rw [Set.mem_preimage, Scheme.Opens.range_ι]
        exact hp
      obtain ⟨q, rfl⟩ := hpU
      obtain ⟨⟨k, x⟩, hkx⟩ := (sigmaMk (fun _ : Fin m => V)).surjective (inv Φ q)
      rw [sigmaMk_mk] at hkx
      refine ⟨Sigma.ι (fun _ : Fin (m + 1) => V) k.succ x, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      show (d k ≫ eU) x = eU q
      rw [hdΦ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hkx, ← Scheme.Hom.comp_apply (inv Φ),
        IsIso.inv_hom_id]
      rfl

end GlobalTheory.EtC.Tr
