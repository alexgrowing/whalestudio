import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pull_eq_of_eq {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e; rfl

private theorem splits_inv (hSP : SplitsPts) {Z Y : Scheme.{0}} (s : Y ⟶ Z) [IsIso s] :
    Splits s (𝟙 Z) (fun _ : Unit => inv s) := by
  refine hSP s (𝟙 Z) Unit _ (fun _ => by simp) ?_
  intro Ω _ _ x y hxy
  refine ⟨(), ?_, fun _ _ => rfl⟩
  rw [← cancel_mono s, hxy]
  simp

theorem UpperTheory.Gal.G3.pCoverInv :
    GalInv.{u} → SplitsPts → CoverInv.{u} := by
  intro hGal hSP k L O _ _ _ _ H θ C hC R _ _ T hT
  have hG := C.isGalois hC
  have ha : ∀ δ, C.a δ ≫ H.q = H.q := by
    intro δ
    obtain ⟨hspl, -⟩ := hG.2.2.2.2.2
    rw [← piK_snd C, ← Category.assoc]
    exact congrArg (· ≫ pullback.snd C.p (gen O k)) (hspl δ)
  refine ⟨hT.inj _ _ (piK C) (piK_snd C) C.Δ C.a hG, fun y hy => ?_⟩
  refine (hGal T hT _ _ (piK C) (piK_snd C) C.Δ C.a ha hG y).2 (fun δ => ?_)
  obtain ⟨g, hiso, hts, hθ⟩ := C.fix δ
  haveI := hiso
  obtain ⟨tr, htr, hfix⟩ := hy g hiso hθ
  have hq : inv (H.s g) ≫ (H.s g ≫ H.q) = H.q := by simp
  have key : ∀ z, tr z = T.pull (inv (H.s g)) hq z := by
    intro z
    have := htr H.Z H.q (𝟙 _) (by simp) Unit (fun _ => inv (H.s g)) (fun _ => hq)
      (splits_inv hSP (H.s g)) z
    rw [T.pull_id] at this
    simpa using this
  have h1 : (H.s g ≫ C.a δ) ≫ H.q = H.s g ≫ H.q := by rw [Category.assoc, ha]
  have h2 : (inv (H.s g) ≫ H.s g) ≫ H.q = H.q := by simp
  have h3 : 𝟙 H.Z ≫ H.q = H.q := by simp
  conv_rhs => rw [← hfix]
  rw [key]
  symm
  calc T.pull (inv (H.s g)) hq (T.pull (H.t g) (H.comm g) y)
      = T.pull (inv (H.s g)) hq (T.pull (H.s g ≫ C.a δ) h1 y) :=
        congrArg _ (pull_eq_of_eq T hts _ h1 y)
    _ = T.pull (inv (H.s g)) hq (T.pull (H.s g) rfl (T.pull (C.a δ) (ha δ) y)) := by
        rw [T.pull_comp (H.s g) (C.a δ) rfl (ha δ) h1]
    _ = T.pull (inv (H.s g) ≫ H.s g) h2 (T.pull (C.a δ) (ha δ) y) :=
        (T.pull_comp _ _ _ _ _ _).symm
    _ = T.pull (𝟙 H.Z) h3 (T.pull (C.a δ) (ha δ) y) :=
        pull_eq_of_eq T (IsIso.inv_hom_id _) _ _ _
    _ = _ := T.pull_id _ _ _
