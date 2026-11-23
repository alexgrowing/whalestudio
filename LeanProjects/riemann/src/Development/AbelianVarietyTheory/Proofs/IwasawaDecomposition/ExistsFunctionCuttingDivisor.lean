import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.SecIdeal

noncomputable section

open GlobalTheory.Cartier

variable {S S' : Scheme.{0}}

theorem gs_pow' (f : S' ⟶ S) (y : S') (U : S.Opens) (h : f y ∈ U) (a : Γ(S, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem dv_germ (g : S' ⟶ S) (Dv : GlobalTheory.EffCartierData S) (x : S') (i i' : Dv.ι)
    (hi : g x ∈ Dv.U i) (hi' : g x ∈ Dv.U i') :
    gs g x (Dv.U i) (Dv.f i) = (gm g x (Dv.U i ⊓ Dv.U i') (Dv.trans i i')).val * gs g x (Dv.U i') (Dv.f i') := by
  have hm : g x ∈ Dv.U i ⊓ Dv.U i' := ⟨hi, hi'⟩
  rw [← gs_res g x inf_le_left hm (Dv.f i)]
  erw [Dv.trans_spec i i']
  rw [gs_mul g x _ hm, gs_unit g x _ hm]
  erw [gs_res g x inf_le_right hm]

theorem e_germ (g : S' ⟶ S) (M : LB S) (V : S'.Opens) (e : ∀ i, Γ(S', V ⊓ (M.pull g).U i))
    (he : e ∈ secOn (M.pull g) V) (x : S') (j j' : PUnit → M.ι)
    (hx : x ∈ V ⊓ (M.pull g).U j) (hx' : x ∈ V ⊓ (M.pull g).U j') :
    (S'.presheaf.germ _ x hx).hom (e j) =
      (gm g x (M.U (j ⟨⟩) ⊓ M.U (j' ⟨⟩)) (M.g (j ⟨⟩) (j' ⟨⟩))).val * (S'.presheaf.germ _ x hx').hom (e j') := by
  have hm : x ∈ V ⊓ (M.pull g).U j ⊓ (M.pull g).U j' := ⟨hx, hx'.2⟩
  have E := congrArg (S'.presheaf.germ _ x hm).hom (he j j')
  rw [map_mul, germ_resG, germ_resG, germ_resG] at E
  refine E.trans (congrArg (· * _) ?_)
  rw [pull_g, val_res]
  refine (germ_resG _ x _ _).trans ?_
  have hg : g x ∈ M.U (j ⟨⟩) ⊓ M.U (j' ⟨⟩) := by
    have h1 := (pull_U M g j).le hx.2
    have h2 := (pull_U M g j').le hx'.2
    exact ⟨h1, h2⟩
  rw [gm_val g x _ hg]
  rfl

theorem sig_germ (g : S' ⟶ S) (M : LB S) (Dv : GlobalTheory.EffCartierData S) (k N : ℕ)
    (σ : (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).Sec) (x : S')
    (p p' : (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).ι)
    (hp : g x ∈ (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).U p)
    (hp' : g x ∈ (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).U p') :
    gs g x _ (σ.f p) =
      (((gm g x (M.U ((p ⟨⟩).1 ⟨⟩) ⊓ M.U ((p' ⟨⟩).1 ⟨⟩)) (M.g _ _)) ^ k *
        (gm g x (Dv.U (p ⟨⟩).2 ⊓ Dv.U (p' ⟨⟩).2) (Dv.trans _ _))⁻¹) ^ N).val * gs g x _ (σ.f p') := by
  have hm : g x ∈ (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).U p ⊓
      (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).U p' := ⟨hp, hp'⟩
  rw [← gs_res g x inf_le_left hm (σ.f p)]
  erw [σ.compat p p']
  rw [gs_mul g x _ hm, gs_unit g x _ hm]
  erw [gs_res g x inf_le_right hm]
  congr 2
  have hq := (lbPow_U (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N p).le hp
  have hq' := (lbPow_U (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N p').le hp'
  have hT : g x ∈ (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)).U (p ⟨⟩) ⊓
      (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)).U (p' ⟨⟩) := ⟨hq, hq'⟩
  rw [lbPow_g (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N p p', map_pow, gm_res g x _ hm, GlobalTheory.CechPic.gm_tens _ _ g x _ _ hq hq']
  have hj : g x ∈ (lbPow M k).U (p ⟨⟩).1 ⊓ (lbPow M k).U (p' ⟨⟩).1 := ⟨hq.1, hq'.1⟩
  have hJ : g x ∈ M.U ((p ⟨⟩).1 ⟨⟩) ⊓ M.U ((p' ⟨⟩).1 ⟨⟩) :=
    ⟨(lbPow_U M k _).le hq.1, (lbPow_U M k _).le hq'.1⟩
  rw [lbPow_g M k (p ⟨⟩).1 (p' ⟨⟩).1, map_pow, gm_res g x _ hj]
  congr 2
  exact map_inv _ _

theorem units_alg {G : Type*} [CommGroup G] (μ τ ε : G) (k N : ℕ) :
    (μ ^ k * τ⁻¹) ^ N * τ ^ N * ((μ * ε)⁻¹) ^ (k * N) = (ε⁻¹) ^ (k * N) := by
  rw [mul_pow, inv_pow, inv_mul_cancel_right, ← pow_mul, ← mul_pow, mul_inv, mul_inv_cancel_left]

theorem ring_alg {R : Type*} [CommRing R] (A B : R) (μ τ ε : Rˣ) (k N : ℕ) :
    (((μ ^ k * τ⁻¹) ^ N : Rˣ) : R) * A * ((τ : R) * B) ^ N * (((μ * ε)⁻¹ : Rˣ) : R) ^ (k * N) =
      A * B ^ N * ((ε⁻¹ : Rˣ) : R) ^ (k * N) := by
  have h := congrArg Units.val (units_alg μ τ ε k N)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  rw [← h]
  ring

theorem glue_germ (X : Scheme.{0}) (V : X.Opens) {κ : Type} (W : κ → X.Opens) (hW : ∀ c, W c ≤ V)
    (hc : ∀ x ∈ V, ∃ c, x ∈ W c) (t : ∀ c, Γ(X, W c))
    (ht : ∀ c c' x (hx : x ∈ W c) (hx' : x ∈ W c'),
      (X.presheaf.germ (W c) x hx).hom (t c) = (X.presheaf.germ (W c') x hx').hom (t c')) :
    ∃ s : Γ(X, V), ∀ c, resG X (hW c) s = t c := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun c => homOfLE (hW c))
    (fun x hx => Opens.mem_iSup.2 (hc x hx)) t (fun c c' => ext_germ fun x hx => by
      have e1 := germ_resG (inf_le_left : W c ⊓ W c' ≤ W c) x hx (t c)
      have e2 := germ_resG (inf_le_right : W c ⊓ W c' ≤ W c') x hx (t c')
      exact e1.trans ((ht c c' x hx.1 hx.2).trans e2.symm))
  exact ⟨s, hs⟩

theorem exists_local_generator_of_sec : ∀ {S S' : Scheme.{0}} (g : S' ⟶ S) (M : LB S) (Dv : GlobalTheory.EffCartierData S) (k N : ℕ)
    (σ : (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).Sec) (V : S'.Opens)
    (e : ∀ i, Γ(S', V ⊓ (M.pull g).U i)), M.IsLB → e ∈ secOn (M.pull g) V → (∀ i, IsUnit (e i)) →
    ∃ t : Γ(S', V), (∀ (A : S'.affineOpens) (hA : A.1 ≤ V), resG S' hA t ∈ ((Dv.idealSheaf ^ N).comap g).ideal A) ∧
      ∀ (A : S'.affineOpens) (hA : A.1 ≤ V), A.1 ≤ g ⁻¹ᵁ nonzeroLocus σ →
        ((Dv.idealSheaf ^ N).comap g).ideal A = Ideal.span {resG S' hA t} := by
  intro S S' g M Dv k N σ V e hM he hu

  have hLU : ∀ p : (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).ι,
      (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).U p =
        M.U ((p ⟨⟩).1 ⟨⟩) ⊓ Dv.U (p ⟨⟩).2 := fun p =>
    (lbPow_U _ N p).trans (congrArg (· ⊓ Dv.U (p ⟨⟩).2) (lbPow_U M k (p ⟨⟩).1))
  let W : (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).ι → S'.Opens :=
    fun p => V ⊓ g ⁻¹ᵁ (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).U p
  have hW : ∀ p, W p ≤ V := fun p => inf_le_left
  have le1 : ∀ p, W p ≤ V ⊓ (M.pull g).U (p ⟨⟩).1 := fun p x hx =>
    ⟨hx.1, (pull_U M g _).ge ((hLU p).le hx.2).1⟩
  have le2 : ∀ p, W p ≤ g ⁻¹ᵁ Dv.U (p ⟨⟩).2 := fun p x hx => ((hLU p).le hx.2).2
  have le3 : ∀ p, W p ≤ g ⁻¹ᵁ (lbPow (GlobalTheory.CechPic.tens (lbPow M k) (GlobalTheory.CechPic.dual Dv.lb)) N).U p :=
    fun p => inf_le_right

  let einv : ∀ j, Γ(S', V ⊓ (M.pull g).U j) := fun j => (((hu j).unit⁻¹ : Γ(S', V ⊓ (M.pull g).U j)ˣ) : Γ(S', _))
  let tp : ∀ p, Γ(S', W p) := fun p =>
    resG S' (le3 p) ((g.app _).hom (σ.f p)) *
      resG S' (le2 p) ((g.app (Dv.U (p ⟨⟩).2)).hom (Dv.f (p ⟨⟩).2)) ^ N *
      resG S' (le1 p) (einv (p ⟨⟩).1) ^ (k * N)

  let εu : ∀ j (x : S') (hx : x ∈ V ⊓ (M.pull g).U j), (S'.presheaf.stalk x)ˣ := fun j x hx =>
    Units.map (S'.presheaf.germ _ x hx).hom.toMonoidHom (hu j).unit
  have hεu : ∀ j x hx, ((εu j x hx : (S'.presheaf.stalk x)ˣ) : S'.presheaf.stalk x) =
      (S'.presheaf.germ _ x hx).hom (e j) := fun j x hx => by
    change (S'.presheaf.germ _ x hx).hom ((hu j).unit : Γ(S', _)) = _
    rw [IsUnit.unit_spec]
  have hεinv : ∀ j x hx, (S'.presheaf.germ _ x hx).hom (einv j) =
      (((εu j x hx)⁻¹ : (S'.presheaf.stalk x)ˣ) : S'.presheaf.stalk x) := fun j x hx => by
    rw [← map_inv]
    rfl
  have hgerm : ∀ p x (hx : x ∈ W p), (S'.presheaf.germ (W p) x hx).hom (tp p) =
      gs g x _ (σ.f p) * gs g x (Dv.U (p ⟨⟩).2) (Dv.f (p ⟨⟩).2) ^ N *
        (((εu _ x (le1 p hx))⁻¹ : (S'.presheaf.stalk x)ˣ) : S'.presheaf.stalk x) ^ (k * N) := by
    intro p x hx
    simp only [tp, map_mul, map_pow]
    rw [germ_resG, germ_resG, germ_resG, gs_eq g x _ hx.2, gs_eq g x _ (le2 p hx)]
    congr 2
  have hε : ∀ (j j' : (M.pull g).ι) (x : S') (hx : x ∈ V ⊓ (M.pull g).U j) (hx' : x ∈ V ⊓ (M.pull g).U j'),
      εu j x hx = gm g x (M.U (j ⟨⟩) ⊓ M.U (j' ⟨⟩)) (M.g (j ⟨⟩) (j' ⟨⟩)) * εu j' x hx' :=
    fun j j' x hx hx' => Units.ext (by
      rw [Units.val_mul, hεu, hεu]
      exact e_germ g M V e he x j j' hx hx')
  have hcompat : ∀ p p' x (hx : x ∈ W p) (hx' : x ∈ W p'),
      (S'.presheaf.germ (W p) x hx).hom (tp p) = (S'.presheaf.germ (W p') x hx').hom (tp p') := by
    intro p p' x hx hx'
    rw [hgerm, hgerm, sig_germ g M Dv k N σ x p p' hx.2 hx'.2,
      dv_germ g Dv x _ _ (le2 p hx) (le2 p' hx'), hε _ _ x (le1 p hx) (le1 p' hx')]
    exact ring_alg _ _ _ _ _ k N
  obtain ⟨t, ht⟩ := glue_germ S' V W hW (fun x hx => by
      obtain ⟨J, hJ⟩ := exists_chart hM (g x)
      obtain ⟨c, hc⟩ := Dv.exists_mem (g x)
      exact ⟨fun _ => ((fun _ => J), c), hx, (hLU _).ge ⟨hJ, hc⟩⟩) tp hcompat
  have germT : ∀ p x (hx : x ∈ W p),
      (S'.presheaf.germ V x (hW p hx)).hom t = (S'.presheaf.germ (W p) x hx).hom (tp p) :=
    fun p x hx => (germ_resG (hW p) x hx t).symm.trans (congrArg _ (ht p))
  have h1 : ∀ (A : S'.affineOpens) (hA : A.1 ≤ V),
      resG S' hA t ∈ ((Dv.idealSheaf ^ N).comap g).ideal A := by
    intro A hA
    rw [← GlobalTheory.EffCartierData.idealSheaf_nsmul, GlobalTheory.EffCartierData.comap_idealSheaf]
    refine (GlobalTheory.EffCartierData.mem_locIdeal_iff _ _ _ _).2 fun c x hxA hc => ?_
    obtain ⟨J, hJ⟩ := exists_chart hM (g x)
    have hxp : x ∈ W (fun _ => ((fun _ => J), c)) := ⟨hA hxA, (hLU _).ge ⟨hJ, hc⟩⟩
    rw [germ_resG, germT _ x hxp, hgerm _ x hxp]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_of_eq ?_) _) _
    rw [← gs_pow' g x (Dv.U c) hc (Dv.f c) N, gs_eq g x (Dv.U c) hc]
    rfl
  refine ⟨t, h1, fun A hA hAσ => le_antisymm ?_ ?_⟩
  · intro a ha
    rw [A.2.mem_ideal_iff]
    intro x hx
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    rw [← GlobalTheory.EffCartierData.idealSheaf_nsmul, GlobalTheory.EffCartierData.comap_idealSheaf] at ha
    replace ha := (GlobalTheory.EffCartierData.mem_locIdeal_iff _ _ _ _).1 ha
    obtain ⟨J, hJ⟩ := exists_chart hM (g x)
    obtain ⟨c, hc⟩ := Dv.exists_mem (g x)
    have hxp : x ∈ W (fun _ => ((fun _ => J), c)) := ⟨hA hx, (hLU _).ge ⟨hJ, hc⟩⟩
    refine Dvd.dvd.trans ?_ (ha c x hx hc)
    have hσu : IsUnit (gs g x _ (σ.f (fun _ => ((fun _ => J), c)))) := by
      have h0 : g x ∈ S.basicOpen (σ.f (fun _ => ((fun _ => J), c))) :=
        (mem_nonzeroLocus_iff σ _ hxp.2).1 (hAσ hx)
      rw [S.mem_basicOpen _ _ hxp.2] at h0
      rw [gs_eq g x _ hxp.2]
      exact (congrArg IsUnit (GlobalTheory.EffCartierData.germ_app g _ x hxp.2)).mpr (h0.map _)
    change (S'.presheaf.germ A.1 x hx).hom (resG S' hA t) ∣ _
    rw [germ_resG, germT _ x hxp, hgerm _ x hxp, IsUnit.mul_right_dvd ((Units.isUnit _).pow _),
      hσu.mul_left_dvd, ← gs_pow' g x (Dv.U c) hc (Dv.f c) N, gs_eq g x (Dv.U c) hc]
    rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h1 A hA

end
end GlobalTheory.SecIdeal
