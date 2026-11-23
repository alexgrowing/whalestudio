import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex Pretriangulated GlobalTheory.EtC

namespace LateralTheory.KummerTheory.NatLESPf
open LateralTheory.KummerTheory.BockCut

theorem exact_transport {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] (eA : A ≃+ A') (eB : B ≃+ B') (eC : C ≃+ C')
    (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
    (hf : ∀ x, eB (f x) = f' (eA x)) (hg : ∀ x, eC (g x) = g' (eB x)) (h : Function.Exact f' g') :
    Function.Exact f g := by
  intro y
  constructor
  · intro hy
    have : g' (eB y) = 0 := by rw [← hg, hy, map_zero]
    obtain ⟨x', hx'⟩ := (h (eB y)).1 this
    refine ⟨eA.symm x', eB.injective ?_⟩
    rw [hf, AddEquiv.apply_symm_apply, hx']
  · rintro ⟨x, rfl⟩
    apply eC.injective
    rw [hg, hf, map_zero]
    exact (h _).2 ⟨_, rfl⟩

theorem NatLES_of (hD : DerDict) : NatLES := by
  intro R _ K
  letI := HasDerivedCategory.standard (Shv R)
  obtain ⟨e, he⟩ := hD R K
  let F := preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj K))
  have hpost : ∀ {X Y : Shv R} (φ : X ⟶ Y) (n : ℤ) (x : HK R K X n),
      e Y n (HK.post R K φ n x) = (F.shift n).map ((DerivedCategory.singleFunctor (Shv R) 0).map φ) (e X n x) := by
    intro X Y φ n x
    rw [he]; rfl
  let d : ∀ (S : ShortComplex (Shv R)), S.ShortExact → ∀ n : ℤ, HK R K S.X₃ n →+ HK R K S.X₁ (n + 1) :=
    fun S hS n => (e S.X₁ (n + 1)).symm.toAddMonoidHom.comp
      ((F.homologySequenceδ hS.singleTriangle n (n + 1) rfl).hom.comp (e S.X₃ n).toAddMonoidHom)
  have hd : ∀ (S : ShortComplex (Shv R)) (hS : S.ShortExact) (n : ℤ) (x : HK R K S.X₃ n),
      e S.X₁ (n + 1) (d S hS n x) = F.homologySequenceδ hS.singleTriangle n (n + 1) rfl (e S.X₃ n x) := by
    intro S hS n x
    exact AddEquiv.apply_symm_apply _ _
  refine ⟨d, fun S hS n => ⟨?_, ?_, ?_⟩, ?_⟩
  · have := F.homologySequence_exact₂ _ hS.singleTriangle_distinguished n
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₁ n) (e S.X₂ n) (e S.X₃ n) _ _ _ _ (hpost _ n) (hpost _ n) this
  · have := F.homologySequence_exact₃ _ hS.singleTriangle_distinguished n (n + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₂ n) (e S.X₃ n) (e S.X₁ (n + 1)) _ _ _ _ (hpost _ n) (hd S hS n) this
  · have := F.homologySequence_exact₁ _ hS.singleTriangle_distinguished n (n + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₃ n) (e S.X₁ (n + 1)) (e S.X₂ (n + 1)) _ _ _ _ (hd S hS n)
      (hpost _ (n + 1)) this
  · intro S T hS hT φ n x
    apply (e T.X₁ (n + 1)).injective
    rw [hpost, hd, hd, hpost]
    have := F.homologySequenceδ_naturality (φ := ShortComplex.ShortExact.singleTriangle.map hS hT φ) (n₀ := n) (n₁ := n + 1) (h := rfl)
    have h2 := ConcreteCategory.congr_hom this
      (show ((F.shift n).obj hS.singleTriangle.obj₃ : Type _) from e S.X₃ n x)
    exact h2.symm
