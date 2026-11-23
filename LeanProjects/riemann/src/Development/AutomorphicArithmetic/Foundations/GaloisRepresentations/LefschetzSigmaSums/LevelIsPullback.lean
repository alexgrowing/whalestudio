import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.G3 (bcMap bcMap_fst bcMap_snd)
open UpperTheory.Gal.Int.Geo (KS Lv)

private theorem level_isPullback {S S' B B' Z : Scheme.{0}} {A : Over S} {A' : Over S'} {s : S ⟶ B'} {s' : S' ⟶ B}
    {f : S' ⟶ S} {g : B ⟶ B'} {φ : A'.left ⟶ A.left} (hφ : φ ≫ A.hom = A'.hom ≫ f)
    (H : IsPullback φ A'.hom A.hom f) (hf : IsPullback f s' s g) (k : ℕ) {q : Z ⟶ B'}
    (e : Z ≅ (GlobalTheory.KS.pow A k).left) (he : e.hom ≫ (GlobalTheory.KS.pow A k).hom ≫ s = q) :
    IsPullback (GlobalTheory.KS.powMap f φ hφ k ≫ e.inv) ((GlobalTheory.KS.pow A' k).hom ≫ s') q g := by
  have P := (GlobalTheory.KS.PowPB.powMap_isPullback S S' A A' f φ hφ H k).paste_vert hf
  have Q : IsPullback e.inv ((GlobalTheory.KS.pow A k).hom ≫ s) q (𝟙 B') := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← he, Category.comp_id, Iso.inv_hom_id_assoc]
  have R := P.paste_horiz Q
  rw [Category.comp_id] at R
  exact R

private theorem pow_square (pc : PowComp) {S₁ S₂ S₁' S₂' : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {A₁' : Over S₁'}
    {A₂' : Over S₂'} {f₁ : S₁' ⟶ S₁} {f₂ : S₂' ⟶ S₂} {π : S₂ ⟶ S₁} {π' : S₂' ⟶ S₁'} {φ₁ : A₁'.left ⟶ A₁.left}
    {φ₂ : A₂'.left ⟶ A₂.left} {χ : A₂.left ⟶ A₁.left} {χ' : A₂'.left ⟶ A₁'.left}
    (h₁ : φ₁ ≫ A₁.hom = A₁'.hom ≫ f₁) (h₂ : φ₂ ≫ A₂.hom = A₂'.hom ≫ f₂)
    (hχ : χ ≫ A₁.hom = A₂.hom ≫ π) (hχ' : χ' ≫ A₁'.hom = A₂'.hom ≫ π')
    (hπ : π' ≫ f₁ = f₂ ≫ π) (hc : χ' ≫ φ₁ = φ₂ ≫ χ) (k : ℕ) :
    GlobalTheory.KS.powMap π' χ' hχ' k ≫ GlobalTheory.KS.powMap f₁ φ₁ h₁ k = GlobalTheory.KS.powMap f₂ φ₂ h₂ k ≫ GlobalTheory.KS.powMap π χ hχ k := by
  have h₃ : (φ₂ ≫ χ) ≫ A₁.hom = A₂'.hom ≫ (f₂ ≫ π) := by
    rw [Category.assoc, hχ, ← Category.assoc, h₂, Category.assoc]
  rw [pc _ _ _ A₂' A₁' A₁ π' f₁ (f₂ ≫ π) χ' φ₁ (φ₂ ≫ χ) hχ' h₁ h₃ hπ hc k,
    pc _ _ _ A₂' A₂ A₁ f₂ π (f₂ ≫ π) φ₂ χ (φ₂ ≫ χ) h₂ hχ h₃ rfl rfl k]

private theorem level_tr {S₁ S₂ S₁' S₂' B B' Z₁ Z₂ : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {A₁' : Over S₁'}
    {A₂' : Over S₂'} {q₁ : Z₁ ⟶ B'} {q₂ : Z₂ ⟶ B'} {g : B ⟶ B'} {k : ℕ} {s₁' : S₁' ⟶ B} {s₂' : S₂' ⟶ B}
    {Φ₁ : (GlobalTheory.KS.pow A₁' k).left ⟶ (GlobalTheory.KS.pow A₁ k).left} {Φ₂ : (GlobalTheory.KS.pow A₂' k).left ⟶ (GlobalTheory.KS.pow A₂ k).left}
    {Ψ : (GlobalTheory.KS.pow A₂ k).left ⟶ (GlobalTheory.KS.pow A₁ k).left} {Ψ' : (GlobalTheory.KS.pow A₂' k).left ⟶ (GlobalTheory.KS.pow A₁' k).left}
    {π' : S₂' ⟶ S₁'} (hΨ' : Ψ' ≫ (GlobalTheory.KS.pow A₁' k).hom = (GlobalTheory.KS.pow A₂' k).hom ≫ π') (hs : π' ≫ s₁' = s₂')
    (hsq : Ψ' ≫ Φ₁ = Φ₂ ≫ Ψ) (e₁ : Z₁ ≅ (GlobalTheory.KS.pow A₁ k).left) (e₂ : Z₂ ≅ (GlobalTheory.KS.pow A₂ k).left)
    (t : Z₂ ⟶ Z₁) (ht : t ≫ q₁ = q₂) (he : t ≫ e₁.hom = e₂.hom ≫ Ψ)
    (P₁ : IsPullback (Φ₁ ≫ e₁.inv) ((GlobalTheory.KS.pow A₁' k).hom ≫ s₁') q₁ g)
    (P₂ : IsPullback (Φ₂ ≫ e₂.inv) ((GlobalTheory.KS.pow A₂' k).hom ≫ s₂') q₂ g) :
    bcMap g t ht ≫ P₁.isoPullback.symm.hom = P₂.isoPullback.symm.hom ≫ Ψ' := by
  have hΨ : Ψ ≫ e₁.inv = e₂.inv ≫ t := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply P₁.hom_ext
  · simp only [Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_fst, bcMap_fst]
    rw [reassoc_of% hsq, hΨ, ← Category.assoc Φ₂ e₂.inv t, IsPullback.isoPullback_inv_fst_assoc]
  · simp only [Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd, bcMap_snd]
    rw [reassoc_of% hΨ', hs, IsPullback.isoPullback_inv_snd]

theorem UpperTheory.Gal.LocalSmoothExtension.kSBc_of :
    ModelBc → LegBc → PowComp → KSBc := by
  intro hmod hleg pc p _ D G L R _ _ gb k T τ gb' hρ ht
  have ht' : ∀ i, gb'.t i = τ.comp (gb.t i) := fun i => RingHom.ext fun c => ht i c
  have hM := fun N : Lv p => hmod D.toG R ℂ τ gb gb' hρ ht' (↑N) (T.M N)
  choose M' f hpb hm using hM
  let m := fun N => (hm N).some
  have hφ : ∀ N, (m N).φ ≫ (T.M N).univ.A.hom = (M' N).univ.A.hom ≫ f N := fun N => (m N).cart.1.w
  have P : ∀ N, IsPullback (GlobalTheory.KS.powMap (f N) (m N).φ (hφ N) k ≫ (T.e N).inv)
      ((GlobalTheory.KS.pow (M' N).univ.A k).hom ≫ (M' N).s) (T.X.q (T.lev N)) (Spec.map (CommRingCat.ofHom τ)) :=
    fun N => level_isPullback (hφ N) (m N).cart.1 (hpb N) k (T.e N) (T.e_q N)
  refine ⟨UpperTheory.Gal.Int.Geo.KS.mk (towerBc T.X (Spec.map (CommRingCat.ofHom τ))) T.lev T.K_eq T.Δ_eq M'
    (fun N => (P N).isoPullback.symm) ?_ ?_, rfl, HEq.rfl⟩
  · intro N
    exact (P N).isoPullback_inv_snd
  · intro N' N h a b
    obtain ⟨π₀, o₀, ψ₀, φ₀, hw₀, hs₀, htr₀, he₀⟩ := T.tr_eq N' N h a b
    obtain ⟨π₁, o₁, ψ₁, φ₁, hs₁, htr₁, hπ, hc⟩ := hleg p D G L R ℂ τ gb gb' hρ ht' N N' (T.M N) (T.M N')
      (M' N) (M' N') (f N) (f N') (hpb N) (hpb N') (m N) (m N') h π₀ o₀ ψ₀ φ₀ hs₀ htr₀
    have hw₁ : (Over.Hom.left ψ₁ ≫ φ₁.φ) ≫ (M' N).univ.A.hom = (M' N').univ.A.hom ≫ π₁ := by
      rw [Category.assoc, φ₁.cart.1.w, ← Category.assoc, Over.w]
    refine ⟨π₁, o₁, ψ₁, φ₁, hw₁, hs₁, htr₁, ?_⟩
    exact level_tr (GlobalTheory.KS.PowPB.powMap_w π₁ _ hw₁ k) hs₁
      (pow_square pc (hφ N) (hφ N') hw₀ hw₁ hπ hc k) (T.e N) (T.e N') _ (T.X.tr_q _ _ h a b) he₀ (P N) (P N')
