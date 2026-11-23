import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pSplitsComp :
    SplitsPts → PtsOfSplits → SplitsComp := by
  intro hS hP Y P Z W κ s _ _ _ _ c I J _ _ τ σ hτ hσ
  have hτc : ∀ i, τ i ≫ s = c := hτ.1
  have hσc : ∀ i j, σ i j ≫ κ = τ i := fun i => (hσ i).1
  refine hS (κ ≫ s) c (I × J) (fun x => σ x.1 x.2)
    (fun x => by rw [← Category.assoc, hσc, hτc]) ?_
  intro Ω _ _ x y hy
  obtain ⟨i, hi, hiu⟩ := hP s c I τ hτ Ω x (y ≫ κ) (by simpa using hy)
  obtain ⟨j, hj, hju⟩ := hP κ (τ i) J (σ i) (hσ i) Ω x y hi.symm
  refine ⟨(i, j), hj, ?_⟩
  rintro ⟨i', j'⟩ h'
  have h'' : x ≫ σ i' j' = y := h'
  have hi' : i' = i := hiu i' (by
    show x ≫ τ i' = y ≫ κ
    rw [← hσc i' j', ← Category.assoc, h''])
  subst hi'
  have hj' : j' = j := hju j' h''
  subst hj'
  rfl
