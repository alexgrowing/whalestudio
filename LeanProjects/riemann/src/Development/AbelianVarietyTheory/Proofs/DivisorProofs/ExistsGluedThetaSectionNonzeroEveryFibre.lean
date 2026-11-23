import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnOfPowOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.KeyTheta

variable {X Y : Scheme.{0}}

abbrev L1 (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)

theorem lineBundle_chart_le_firstPower_chart (L : LB X) (i : L.ι) : L.U i ≤ (L1 L).U (fun _ => i) :=
  fun _ hx => Set.mem_iInter.2 fun _ => hx

def prodSec (π : X ⟶ Y) (L : LB X) (δ : LB Y) {W N : Y.Opens} (hNW : N ≤ W)
    (σ : ∀ j, Γ(X, π ⁻¹ᵁ W ⊓ (L1 L).U j)) (t : δ.Sec) :
    ∀ p : (CechPic.tens L (δ.pull π)).ι, Γ(X, π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U p) :=
  fun p => resG X (le_inf (inf_le_left.trans (fun _ hx => hNW hx)) (inf_le_right.trans (inf_le_left.trans (lineBundle_chart_le_firstPower_chart L p.1))) :
        π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U p ≤ π ⁻¹ᵁ W ⊓ (L1 L).U (fun _ => p.1)) (σ (fun _ => p.1)) *
    resG X (inf_le_right.trans inf_le_right :
        π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U p ≤ LB.wchart δ (fun _ : PUnit => π) p.2)
      ((π.appLE (δ.U (p.2 PUnit.unit)) _ (LB.wchart_le δ (fun _ => π) p.2 PUnit.unit)).hom (t.f (p.2 PUnit.unit)))

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ZH.ThetaSys o Ω} {ρ : S.Real} {M : ZH.RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

def toPre (Zh : ZH.ZHOut ρ M U₀ EE) : ZH.ZHPre ρ M U₀ :=
  ⟨Zh.u₀, Zh.u₀_gen, Zh.G, Zh.semi, Zh.dim, Zh.qproj, Zh.φ, Zh.cart, Zh.L, Zh.cub, Zh.sym, Zh.w, Zh.w_gen, Zh.w_rig,
    Zh.split⟩

end GlobalTheory.KeyTheta

theorem GlobalTheory.KeyTheta.prodSec_mem : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (L : LB X) (δ : LB Y) {W N : Y.Opens} (hNW : N ≤ W) (σ : ∀ j, Γ(X, π ⁻¹ᵁ W ⊓ (GlobalTheory.KeyTheta.L1 L).U j)) (t : δ.Sec), σ ∈ secOn (GlobalTheory.KeyTheta.L1 L) (π ⁻¹ᵁ W) → GlobalTheory.KeyTheta.prodSec π L δ hNW σ t ∈ secOn (CechPic.tens L (δ.pull π)) (π ⁻¹ᵁ N) := by
  intro X Y π L δ W N hNW σ t hσ
  have rr : ∀ {A B C : X.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(X, A)),
      resG X e' (resG X e s) = resG X (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  have ar : ∀ {U : Y.Opens} {V V' : X.Opens} (e : V ≤ π ⁻¹ᵁ U) (h : V' ≤ V) (x : Γ(Y, U)),
      resG X h ((π.appLE U V e).hom x) = (π.appLE U V' (h.trans e)).hom x := fun e h x => by
    change (π.appLE _ _ e ≫ X.presheaf.map (homOfLE h).op).hom x = _
    rw [Scheme.Hom.appLE_map]
  have ra : ∀ {U U' : Y.Opens} {V : X.Opens} (h : U' ≤ U) (e : V ≤ π ⁻¹ᵁ U') (x : Γ(Y, U)),
      (π.appLE U' V e).hom (resG Y h x) = (π.appLE U V (fun _ hx => h (e hx))).hom x := fun h e x => by
    change (Y.presheaf.map (homOfLE h).op ≫ π.appLE _ _ e).hom x = _
    rw [Scheme.Hom.map_appLE]
  rintro ⟨i, j⟩ ⟨i', j'⟩
  have hO1 : π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j') ≤
      π ⁻¹ᵁ (δ.U (j PUnit.unit) ⊓ δ.U (j' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1.2.2 PUnit.unit, Set.mem_iInter.1 hx.2.2 PUnit.unit⟩
  have ht := congrArg (π.appLE _ _ hO1).hom (t.compat (j PUnit.unit) (j' PUnit.unit))
  rw [map_mul] at ht
  change (π.appLE _ _ hO1).hom (resG Y _ _) = (π.appLE _ _ hO1).hom _ * (π.appLE _ _ hO1).hom (resG Y _ _) at ht
  rw [ra, ra] at ht
  have hs := LB.secOn_rel hσ (fun _ => i) (fun _ => i')
    (W := π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j'))
    (le_inf (fun x hx => hNW hx.1.1) (fun x hx => lineBundle_chart_le_firstPower_chart L i hx.1.2.1))
    (le_inf (fun x hx => hNW hx.1.1) (fun x hx => lineBundle_chart_le_firstPower_chart L i' hx.2.1))
    (le_inf (fun x hx => lineBundle_chart_le_firstPower_chart L i hx.1.2.1) (fun x hx => lineBundle_chart_le_firstPower_chart L i' hx.2.1))
  have hg : ∀ (h : π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j') ≤
      (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j')),
      resG X h ((CechPic.tens L (δ.pull π)).g (i, j) (i', j') : Γ(X, _)) =
        resG X (fun x hx => ⟨hx.1.2.1, hx.2.1⟩ : π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j') ≤ L.U i ⊓ L.U i') (L.g i i' : Γ(X, L.U i ⊓ L.U i')) *
        (π.appLE _ _ hO1).hom (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(Y, _)) := by
    intro h
    have e1 : ((CechPic.tens L (δ.pull π)).g (i, j) (i', j') : Γ(X, _)) =
      resG X (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j') ≤ L.U i ⊓ L.U i')
          (L.g i i' : Γ(X, L.U i ⊓ L.U i')) *
      resG X (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j') ≤ (δ.pull π).U j ⊓ (δ.pull π).U j')
          ((δ.pull π).g j j' : Γ(X, (δ.pull π).U j ⊓ (δ.pull π).U j')) := rfl
    have e2 : ((δ.pull π).g j j' : Γ(X, (δ.pull π).U j ⊓ (δ.pull π).U j')) =
        (π.appLE _ _ (fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩ :
          (δ.pull π).U j ⊓ (δ.pull π).U j' ≤ π ⁻¹ᵁ (δ.U (j PUnit.unit) ⊓ δ.U (j' PUnit.unit)))).hom
          (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(Y, δ.U (j PUnit.unit) ⊓ δ.U (j' PUnit.unit))) := by
      simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
      rfl
    rw [e1, map_mul, rr, e2, rr]
    congr 1
    exact ar _ _ _
  have hl : ∀ (h : π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j') ≤
      (L1 L).U (fun _ => i) ⊓ (L1 L).U (fun _ => i')),
      resG X h ((L1 L).g (fun _ => i) (fun _ => i') : Γ(X, _)) =
        resG X (fun x hx => ⟨hx.1.2.1, hx.2.1⟩ : π ⁻¹ᵁ N ⊓ (CechPic.tens L (δ.pull π)).U (i, j) ⊓ (CechPic.tens L (δ.pull π)).U (i', j') ≤ L.U i ⊓ L.U i') (L.g i i' : Γ(X, L.U i ⊓ L.U i')) := by
    intro h
    simp only [L1, LB.LinComb, Fin.prod_univ_one, zpow_one]
    exact rr _ _ _
  rw [hl] at hs
  dsimp only [prodSec]
  rw [hg]
  simp only [map_mul, rr, ar]
  rw [hs, ht]
  ring

theorem GlobalTheory.KeyTheta.prodSec_fib : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (L : LB X) (δ : LB Y) {W : Y.Opens} (σ : ∀ j, Γ(X, π ⁻¹ᵁ W ⊓ (GlobalTheory.KeyTheta.L1 L).U j)) (t : δ.Sec), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y), Set.range x ⊆ W → ∃ (g : Sp K ⟶ X) (j : (GlobalTheory.KeyTheta.L1 L).ι), g ≫ π = x ∧ valF g _ (σ j) ≠ 0) → ∀ (k : δ.ι) (hk : Y.basicOpen (t.f k) ≤ W) (y : Y), y ∈ Y.basicOpen (t.f k) → ∃ (z : X) (p : (CechPic.tens L (δ.pull π)).ι), π z = y ∧ z ∈ X.basicOpen (GlobalTheory.KeyTheta.prodSec π L δ hk σ t p) := by
  intro X Y π L δ W σ t hne k hk y hy
  obtain ⟨K, _, _, x, hx⟩ := GlobalTheory.TripleOut.exists_geomPoint y
  obtain ⟨g, j, hg, hv⟩ := hne K x (by rintro _ ⟨w, rfl⟩; rw [hx]; exact hk hy)
  have hzy : π (g (IsLocalRing.closedPoint K)) = y :=
    (Scheme.Hom.comp_apply g π _).symm.trans (hg ▸ hx _)
  have hz1 : g (IsLocalRing.closedPoint K) ∈ X.basicOpen (σ j) := GlobalTheory.TripleOut.mem_basicOpen_of_valF g (σ j) hv _
  obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun m => congrArg j (Subsingleton.elim _ _)⟩
  have hyb : π (g (IsLocalRing.closedPoint K)) ∈ Y.basicOpen (t.f k) := by rw [hzy]; exact hy
  have hyk : π (g (IsLocalRing.closedPoint K)) ∈ δ.U k := Y.basicOpen_le _ hyb
  have hw : g (IsLocalRing.closedPoint K) ∈ LB.wchart δ (fun _ : PUnit => π) (fun _ => k) := Set.mem_iInter.2 fun _ => hyk
  have hV : g (IsLocalRing.closedPoint K) ∈
      π ⁻¹ᵁ Y.basicOpen (t.f k) ⊓ (CechPic.tens L (δ.pull π)).U (i, fun _ => k) :=
    ⟨hyb, Set.mem_iInter.1 (X.basicOpen_le _ hz1).2 0, hw⟩
  refine ⟨g (IsLocalRing.closedPoint K), (i, fun _ => k), hzy, ?_⟩
  refine (Scheme.basicOpen_mul X _ _).ge ⟨(Scheme.basicOpen_res X _ _).ge ⟨hV, hz1⟩, (Scheme.basicOpen_res X _ _).ge ⟨hV, ?_⟩⟩
  exact (Scheme.basicOpen_appLE π _ _ _ _).ge ⟨hw, hyb⟩

theorem GlobalTheory.KeyTheta.sec_of_secOn_top : ∀ {X : Scheme.{0}} (B : LB X) (τ : ∀ p, Γ(X, ⊤ ⊓ B.U p)), τ ∈ secOn B ⊤ → ∃ s : B.Sec, ∀ p, ∀ z ∈ X.basicOpen (τ p), z ∈ nonzeroLocus s := by
  intro X B τ hτ
  have rr : ∀ {A B C : X.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(X, A)),
      resG X e' (resG X e s) = resG X (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  refine ⟨⟨fun i => resG X (le_inf le_top le_rfl : B.U i ≤ ⊤ ⊓ B.U i) (τ i), fun i j => ?_⟩, fun p z hz => ?_⟩
  · have h := congrArg (resG X (le_inf (le_inf le_top inf_le_left) inf_le_right : B.U i ⊓ B.U j ≤ ⊤ ⊓ B.U i ⊓ B.U j)) (hτ i j)
    rw [map_mul, rr, rr, rr] at h
    change resG X _ (resG X _ (τ i)) = (B.g i j : Γ(X, B.U i ⊓ B.U j)) * resG X _ (resG X _ (τ j))
    rw [rr, rr, h]
    congr 1
    have e : (homOfLE (le_rfl : B.U i ⊓ B.U j ≤ B.U i ⊓ B.U j)).op = 𝟙 _ := rfl
    change (X.presheaf.map (homOfLE _).op).hom _ = _
    rw [e, X.presheaf.map_id]; rfl
  · refine TopologicalSpace.Opens.mem_iSup.2 ⟨p, ?_⟩
    change z ∈ X.basicOpen (resG X _ (τ p))
    rw [Scheme.basicOpen_res]
    exact ⟨(X.basicOpen_le (τ p) hz).2, hz⟩

theorem GlobalTheory.KeyTheta.ratio_exists : ∀ {Y : Scheme.{0}} (δ : LB Y) (ta tb : δ.Sec) (k : δ.ι) (M₀ : Y.Opens), M₀ ≤ Y.basicOpen (ta.f k) → ∃ u : Γ(Y, M₀), ∀ j, resG Y (inf_le_left : M₀ ⊓ δ.U j ≤ M₀) u * resG Y (inf_le_right : M₀ ⊓ δ.U j ≤ δ.U j) (ta.f j) = resG Y (inf_le_right : M₀ ⊓ δ.U j ≤ δ.U j) (tb.f j) := by
  intro Y δ ta tb k M₀ hM
  have rr : ∀ {A B C : Y.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(Y, A)),
      resG Y e' (resG Y e s) = resG Y (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  have hMk : M₀ ≤ δ.U k := hM.trans (Y.basicOpen_le _)
  have hunit : IsUnit (resG Y hMk (ta.f k)) := by
    have h1 := (RingedSpace.isUnit_res_basicOpen Y.toLocallyRingedSpace.toRingedSpace (ta.f k)).map (resG Y hM)
    change IsUnit (resG Y hM (resG Y (Y.basicOpen_le (ta.f k)) (ta.f k))) at h1
    rwa [rr] at h1
  obtain ⟨v, hv⟩ := hunit
  refine ⟨resG Y hMk (tb.f k) * ↑v⁻¹, fun j => ?_⟩
  have e : M₀ ⊓ δ.U j ≤ δ.U j ⊓ δ.U k := fun x hx => ⟨hx.2, hMk hx.1⟩
  have ca := congrArg (resG Y e) (ta.compat j k)
  have cb := congrArg (resG Y e) (tb.compat j k)
  change resG Y e (resG Y _ (ta.f j)) = resG Y e (_ * resG Y _ (ta.f k)) at ca
  change resG Y e (resG Y _ (tb.f j)) = resG Y e (_ * resG Y _ (tb.f k)) at cb
  rw [map_mul, rr, rr] at ca cb
  rw [ca, cb, map_mul]
  have hk1 : resG Y (fun x hx => hMk hx.1 : M₀ ⊓ δ.U j ≤ δ.U k) (ta.f k) =
      resG Y (inf_le_left : M₀ ⊓ δ.U j ≤ M₀) (v : Γ(Y, M₀)) := by rw [hv, rr]
  have hk2 : resG Y (fun x hx => hMk hx.1 : M₀ ⊓ δ.U j ≤ δ.U k) (tb.f k) =
      resG Y (inf_le_left : M₀ ⊓ δ.U j ≤ M₀) (resG Y hMk (tb.f k)) := by rw [rr]
  have hinv : resG Y (inf_le_left : M₀ ⊓ δ.U j ≤ M₀) ((v⁻¹ : (Γ(Y, M₀))ˣ) : Γ(Y, M₀)) *
      resG Y (inf_le_left : M₀ ⊓ δ.U j ≤ M₀) (v : Γ(Y, M₀)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [hk1, hk2]
  linear_combination (resG Y e (δ.g j k : Γ(Y, δ.U j ⊓ δ.U k)) *
    resG Y (inf_le_left : M₀ ⊓ δ.U j ≤ M₀) (resG Y hMk (tb.f k))) * hinv

theorem GlobalTheory.KeyTheta.ratio_value : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (δ : LB M.Z) {I : Type} (t : I → δ.Sec) (th : I → Ω), ZM.SecCoord δ t M.pt th → ∀ (a b : I) (k l : δ.ι) (M₀ : M.Z.Opens), (M₀ : Set M.Z).Nonempty → M₀ ≤ M.Z.basicOpen ((t a).f k) → M₀ ≤ M.Z.basicOpen ((t b).f l) → ∀ u : Γ(M.Z, M₀), (∀ j, resG M.Z (inf_le_left : M₀ ⊓ δ.U j ≤ M₀) u * resG M.Z (inf_le_right : M₀ ⊓ δ.U j ≤ δ.U j) ((t a).f j) = resG M.Z (inf_le_right : M₀ ⊓ δ.U j ≤ δ.U j) ((t b).f j)) → th a ≠ 0 ∧ th b ≠ 0 ∧ valF M.pt M₀ u = th b / th a := by
  intro o Ω _ _ _ M δ I t th hsc a b k l M₀ hne hk hl u hu
  obtain ⟨τ, -, hτ⟩ := hsc
  have hV : ∀ m : δ.ι, M₀ ≤ δ.U m → ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (δ.pull M.pt).U (fun _ => m) := fun m hm x _ =>
    Set.mem_iInter.2 fun _ => M.top_le_preimage_pt (hne.mono hm) (x := x) trivial
  have key : ∀ (i : I) (m : δ.ι), M₀ ≤ δ.U m → valF M.pt (δ.U m) ((t i).f m) =
      th i * valR (𝟙 (Sp Ω)) _ (τ.s (fun _ => m)).val := by
    intro i m hm
    have hw : (δ.pull M.pt).U (fun _ => m) ≤ M.pt ⁻¹ᵁ δ.U m := LB.wchart_le δ _ _ PUnit.unit
    have h := congrArg (valR (𝟙 (Sp Ω)) _) (hτ i (fun _ => m) hw)
    rw [GlobalTheory.Points.valR_appLE _ _ _ (hV m hm), Category.id_comp, GlobalTheory.Points.valR_mul _ _ (hV m hm),
      GlobalTheory.Points.valR_res _ _ (hV m hm)] at h
    have hs : valR (𝟙 (Sp Ω)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (th i)) = th i := by
      have := GlobalTheory.Points.valR_specMap (𝟙 (CommRingCat.of Ω)) (th i)
      rw [Spec.map_id] at this
      exact this
    rw [hs] at h
    exact h
  have cne : ∀ m : δ.ι, M₀ ≤ δ.U m → valR (𝟙 (Sp Ω)) _ (τ.s (fun _ => m)).val ≠ 0 := by
    intro m hm
    rw [GlobalTheory.Points.valR_eq _ _ (hV m hm)]
    exact ((τ.s _).isUnit.map _).ne_zero
  have hMk : M₀ ≤ δ.U k := hk.trans (M.Z.basicOpen_le _)
  have hMl : M₀ ≤ δ.U l := hl.trans (M.Z.basicOpen_le _)
  have unitVal : ∀ (i : I) (m : δ.ι), M₀ ≤ M.Z.basicOpen ((t i).f m) → valF M.pt (δ.U m) ((t i).f m) ≠ 0 := by
    intro i m hm
    have hp : ⊤ ≤ M.pt ⁻¹ᵁ δ.U m := M.top_le_preimage_pt (hne.mono (hm.trans (M.Z.basicOpen_le _)))
    have hb := M.top_le_preimage_pt (hne.mono hm)
    exact ((GlobalTheory.Points.le_preimage_basicOpen_iff M.pt hp _).1 hb).ne_zero
  have ha : th a ≠ 0 := fun h0 => unitVal a k hk (by rw [key a k hMk, h0, zero_mul])
  have hb : th b ≠ 0 := fun h0 => unitVal b l hl (by rw [key b l hMl, h0, zero_mul])
  refine ⟨ha, hb, ?_⟩
  have hne' : ((M₀ ⊓ δ.U k : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [inf_eq_left.2 hMk]; exact hne
  have h := congrArg (valF M.pt (M₀ ⊓ δ.U k)) (hu k)
  change valR M.pt _ (_ * _) = _ at h
  rw [GlobalTheory.Points.valR_mul _ _ (M.top_le_preimage_pt hne')] at h
  change valF M.pt _ _ * valF M.pt _ _ = valF M.pt _ _ at h
  rw [M.valF_resG _ hne', M.valF_resG _ hne', M.valF_resG _ hne', key a k hMk, key b k hMk] at h
  have hc := cne k hMk
  rw [eq_div_iff ha]
  exact mul_right_cancel₀ hc (by rw [← h]; ring)

theorem GlobalTheory.KeyTheta.theta_ratio : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (a b : S.Gam) (W W' M₀ : M.Z.Opens) (hW : M₀ ≤ W) (hW' : M₀ ≤ W') (σ : ∀ j, Γ(Zh.G.left, Zh.G.hom ⁻¹ᵁ W ⊓ (GlobalTheory.KeyTheta.L1 Zh.L.L).U j)) (σ' : ∀ j, Γ(Zh.G.left, Zh.G.hom ⁻¹ᵁ W' ⊓ (GlobalTheory.KeyTheta.L1 Zh.L.L).U j)), ZH.GenVal ρ M U₀ Zh.u₀ Zh.G Zh.φ Zh.L.L Zh.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th a)⁻¹) _ σ → ZH.GenVal ρ M U₀ Zh.u₀ Zh.G Zh.φ Zh.L.L Zh.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th b)⁻¹) _ σ' → (M₀ : Set M.Z).Nonempty → ∀ u : Γ(M.Z, M₀), S.th a ≠ 0 → S.th b ≠ 0 → valF M.pt M₀ u = S.th b / S.th a → ∀ (j : (GlobalTheory.KeyTheta.L1 Zh.L.L).ι) (V : Zh.G.left.Opens) (hV : V ≤ Zh.G.hom ⁻¹ᵁ M₀ ⊓ (GlobalTheory.KeyTheta.L1 Zh.L.L).U j), resG Zh.G.left (fun x hx => ⟨hW (hV hx).1, (hV hx).2⟩ : V ≤ Zh.G.hom ⁻¹ᵁ W ⊓ (GlobalTheory.KeyTheta.L1 Zh.L.L).U j) (σ j) = (Zh.G.hom.appLE M₀ V (hV.trans inf_le_left)).hom u * resG Zh.G.left (fun x hx => ⟨hW' (hV hx).1, (hV hx).2⟩ : V ≤ Zh.G.hom ⁻¹ᵁ W' ⊓ (GlobalTheory.KeyTheta.L1 Zh.L.L).U j) (σ' j) := by
  intro o Ω _ _ _ S ρ M U₀ EE Zh hU a b W W' M₀ hW hW' σ σ' hg hg' hne u ha hb hv j V hV
  have rr : ∀ {A B C : Zh.G.left.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(Zh.G.left, A)),
      resG Zh.G.left e' (resG Zh.G.left e s) = resG Zh.G.left (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  have ar : ∀ {U : M.Z.Opens} {V V' : Zh.G.left.Opens} (e : V ≤ Zh.G.hom ⁻¹ᵁ U) (h : V' ≤ V) (x : Γ(M.Z, U)),
      resG Zh.G.left h ((Zh.G.hom.appLE U V e).hom x) = (Zh.G.hom.appLE U V' (h.trans e)).hom x := fun e h x => by
    change (Zh.G.hom.appLE _ _ e ≫ Zh.G.left.presheaf.map (homOfLE h).op).hom x = _
    rw [Scheme.Hom.appLE_map]
  let Q : ZH.ZHPre ρ M U₀ := toPre Zh
  have g1 := Q.genVal_res 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th a)⁻¹)
    (V := Zh.G.hom ⁻¹ᵁ W) (V' := Zh.G.hom ⁻¹ᵁ M₀) (fun x hx => hW hx) σ hg
  have g2 := Q.genVal_res 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th b)⁻¹)
    (V := Zh.G.hom ⁻¹ᵁ W') (V' := Zh.G.hom ⁻¹ᵁ M₀) (fun x hx => hW' hx) σ' hg'
  have g3 := Q.genVal_sum 1 (I := Unit) (J := Unit) (fun _ => ρ.th₁) (fun _ _ => (S.th b)⁻¹) M₀ hne (fun _ => u)
    (fun _ => _) (fun _ => g2)
  have hcoef : (fun _ : Unit => ∑ _i : Unit, valF M.pt M₀ ((fun _ : Unit => u) _i) * (S.th b)⁻¹) =
      fun _ => (S.th a)⁻¹ := by
    funext
    simp only [Finset.univ_unique, Finset.sum_singleton, hv]
    field_simp
  rw [hcoef] at g3
  have heq := congrFun (Q.eq_of_genVal hU 1 _ _ _ _ _ g1 g3) j
  have heq' : resG Zh.G.left (fun x hx => ⟨hW hx.1, hx.2⟩ :
        Zh.G.hom ⁻¹ᵁ M₀ ⊓ (L1 Zh.L.L).U j ≤ Zh.G.hom ⁻¹ᵁ W ⊓ (L1 Zh.L.L).U j) (σ j) =
      resG Zh.G.left (inf_le_left : Zh.G.hom ⁻¹ᵁ M₀ ⊓ (L1 Zh.L.L).U j ≤ Zh.G.hom ⁻¹ᵁ M₀)
        ((Zh.G.hom.appLE M₀ (Zh.G.hom ⁻¹ᵁ M₀) le_rfl).hom u) *
      resG Zh.G.left (fun x hx => ⟨hW' hx.1, hx.2⟩ :
        Zh.G.hom ⁻¹ᵁ M₀ ⊓ (L1 Zh.L.L).U j ≤ Zh.G.hom ⁻¹ᵁ W' ⊓ (L1 Zh.L.L).U j) (σ' j) := by
    have h := heq
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    exact h
  rw [← rr (fun x hx => ⟨hW hx.1, hx.2⟩ :
    Zh.G.hom ⁻¹ᵁ M₀ ⊓ (L1 Zh.L.L).U j ≤ Zh.G.hom ⁻¹ᵁ W ⊓ (L1 Zh.L.L).U j) hV, heq', map_mul, rr, ar]
  congr 1
  exact rr _ _ _

theorem GlobalTheory.KeyTheta.prodSec_agree : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), ZM.SecCoord δ t M.pt S.th → ∀ (a b : S.Gam) (W W' : M.Z.Opens) (σ : ∀ j, Γ(Zh.G.left, Zh.G.hom ⁻¹ᵁ W ⊓ (GlobalTheory.KeyTheta.L1 Zh.L.L).U j)) (σ' : ∀ j, Γ(Zh.G.left, Zh.G.hom ⁻¹ᵁ W' ⊓ (GlobalTheory.KeyTheta.L1 Zh.L.L).U j)), σ ∈ secOn (GlobalTheory.KeyTheta.L1 Zh.L.L) (Zh.G.hom ⁻¹ᵁ W) → σ' ∈ secOn (GlobalTheory.KeyTheta.L1 Zh.L.L) (Zh.G.hom ⁻¹ᵁ W') → ZH.GenVal ρ M U₀ Zh.u₀ Zh.G Zh.φ Zh.L.L Zh.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th a)⁻¹) _ σ → ZH.GenVal ρ M U₀ Zh.u₀ Zh.G Zh.φ Zh.L.L Zh.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th b)⁻¹) _ σ' → ∀ (k l : δ.ι) (hk : M.Z.basicOpen ((t a).f k) ≤ W) (hl : M.Z.basicOpen ((t b).f l) ≤ W') (p : (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).ι), resG Zh.G.left (inf_le_inf_right _ inf_le_left : (Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t a).f k) ⊓ Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t b).f l)) ⊓ (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).U p ≤ Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t a).f k) ⊓ (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).U p) (GlobalTheory.KeyTheta.prodSec Zh.G.hom Zh.L.L δ hk σ (t a) p) = resG Zh.G.left (inf_le_inf_right _ inf_le_right : (Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t a).f k) ⊓ Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t b).f l)) ⊓ (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).U p ≤ Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t b).f l) ⊓ (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).U p) (GlobalTheory.KeyTheta.prodSec Zh.G.hom Zh.L.L δ hl σ' (t b) p) := by
  intro o Ω _ _ _ S ρ M U₀ EE Zh hU δ t hsc a b W W' σ σ' hσ hσ' hg hg' k l hk hl p
  have rr : ∀ {A B C : Zh.G.left.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(Zh.G.left, A)),
      resG Zh.G.left e' (resG Zh.G.left e s) = resG Zh.G.left (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  have ar : ∀ {U : M.Z.Opens} {V V' : Zh.G.left.Opens} (e : V ≤ Zh.G.hom ⁻¹ᵁ U) (h : V' ≤ V) (x : Γ(M.Z, U)),
      resG Zh.G.left h ((Zh.G.hom.appLE U V e).hom x) = (Zh.G.hom.appLE U V' (h.trans e)).hom x := fun e h x => by
    change (Zh.G.hom.appLE _ _ e ≫ Zh.G.left.presheaf.map (homOfLE h).op).hom x = _
    rw [Scheme.Hom.appLE_map]
  have ra : ∀ {U U' : M.Z.Opens} {V : Zh.G.left.Opens} (h : U' ≤ U) (e : V ≤ Zh.G.hom ⁻¹ᵁ U') (x : Γ(M.Z, U)),
      (Zh.G.hom.appLE U' V e).hom (resG M.Z h x) = (Zh.G.hom.appLE U V (fun _ hx => h (e hx))).hom x := fun h e x => by
    change (M.Z.presheaf.map (homOfLE h).op ≫ Zh.G.hom.appLE _ _ e).hom x = _
    rw [Scheme.Hom.map_appLE]
  obtain ⟨i, jj⟩ := p
  by_cases hne : ((M.Z.basicOpen ((t a).f k) ⊓ M.Z.basicOpen ((t b).f l) : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · refine Zh.G.left.sheaf.eq_of_locally_eq' (fun e : Empty => e.elim) _ (fun e => e.elim) (fun x hx => ?_) _ _
      (fun e => e.elim)
    exact (hne ⟨Zh.G.hom x, hx.1.1, hx.1.2⟩).elim
  set M₀ : M.Z.Opens := M.Z.basicOpen ((t a).f k) ⊓ M.Z.basicOpen ((t b).f l) with hM₀
  obtain ⟨u, hu⟩ := GlobalTheory.KeyTheta.ratio_exists δ (t a) (t b) k M₀ inf_le_left
  obtain ⟨ha, hb, hv⟩ := GlobalTheory.KeyTheta.ratio_value o Ω M δ t S.th hsc a b k l M₀ hne inf_le_left inf_le_right u hu
  have hO : Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t a).f k) ⊓ Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t b).f l) ⊓
      (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).U (i, jj) ≤ Zh.G.hom ⁻¹ᵁ M₀ ⊓ (L1 Zh.L.L).U (fun _ => i) :=
    fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, lineBundle_chart_le_firstPower_chart Zh.L.L i hx.2.1⟩
  have h1 := GlobalTheory.KeyTheta.theta_ratio o Ω S ρ M U₀ EE Zh hU a b W W' M₀ (inf_le_left.trans hk) (inf_le_right.trans hl) σ σ' hg hg' hne u ha hb hv
    (fun _ => i) _ hO
  have hδ : Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t a).f k) ⊓ Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t b).f l) ⊓
      (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).U (i, jj) ≤ Zh.G.hom ⁻¹ᵁ (M₀ ⊓ δ.U (jj PUnit.unit)) :=
    fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, Set.mem_iInter.1 hx.2.2 PUnit.unit⟩
  have h2 := congrArg (Zh.G.hom.appLE _ _ hδ).hom (hu (jj PUnit.unit))
  simp only [map_mul, ra] at h2
  dsimp only [prodSec]
  simp only [map_mul, rr, ar]
  rw [h1, ← h2]
  ring

theorem GlobalTheory.KeyTheta.exists_nzFib : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → (∀ a, ∀ z ∈ nonzeroLocus (t a), a ∈ S.supI M z) → ∃ σ : (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).Sec, NzFib σ := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hO δ t hδ hcov hsc hsup
  choose σ hσ hg hne using fun a => Zh.theta (nonzeroLocus (t a)) a (hsup a)
  have hle : ∀ q : S.Gam × δ.ι, M.Z.basicOpen ((t q.1).f q.2) ≤ nonzeroLocus (t q.1) := fun q =>
    le_iSup (fun k => M.Z.basicOpen ((t q.1).f k)) q.2
  have hcovY : ∀ y : M.Z, ∃ q : S.Gam × δ.ι, y ∈ M.Z.basicOpen ((t q.1).f q.2) := by
    intro y
    have hy : y ∈ (⨆ a, nonzeroLocus (t a)) := hcov ▸ trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ha
    exact ⟨(a, k), hk⟩
  obtain ⟨τ, hτ, hres⟩ := ZH.exists_secOn_glue (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)) ⊤
    (fun q : S.Gam × δ.ι => Zh.G.hom ⁻¹ᵁ M.Z.basicOpen ((t q.1).f q.2)) (fun _ => le_top)
    (fun x _ => hcovY (Zh.G.hom x))
    (fun q => GlobalTheory.KeyTheta.prodSec Zh.G.hom Zh.L.L δ (hle q) (σ q.1) (t q.1))
    (fun q => GlobalTheory.KeyTheta.prodSec_mem Zh.G.hom Zh.L.L δ (hle q) (σ q.1) (t q.1) (hσ q.1))
    (fun q q' p => GlobalTheory.KeyTheta.prodSec_agree o Ω S ρ M U₀ EE Zh hO.ne δ t hsc q.1 q'.1 _ _ (σ q.1) (σ q'.1) (hσ q.1) (hσ q'.1) (hg q.1) (hg q'.1)
      q.2 q'.2 (hle q) (hle q') p)
  obtain ⟨s, hs⟩ := GlobalTheory.KeyTheta.sec_of_secOn_top _ τ hτ
  refine ⟨s, fun y => ?_⟩
  obtain ⟨q, hq⟩ := hcovY y
  obtain ⟨z, p, hz, hzb⟩ := GlobalTheory.KeyTheta.prodSec_fib Zh.G.hom Zh.L.L δ (σ q.1) (t q.1) (hne q.1) q.2 (hle q) y hq
  refine ⟨z, hz, hs p z ?_⟩
  rw [← hres q p, Scheme.basicOpen_res] at hzb
  exact hzb.2

end
