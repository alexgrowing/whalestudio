import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrix

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.ExpDirs

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc ReciprocityTheory.ChartRestriction.G.PullbackSections Filter
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isDerivAt0_of_comb {X : Scheme.{0}} {t : SAB H X} {x : Sp ℂ ⟶ X} {g m : ℕ}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)} (e0 : e 0 = (1 : Over.mk x ⟶ t.G).left)
    {v : Fin m → (Sp (DualNumber ℂ) ⟶ t.G.left)} {w : Fin m → Fin g → ℂ} (ht : ∀ i, IsTanAtG t x (v i))
    (hv : ∀ i, IsDerivAt0 e (w i) (v i)) {a : Fin m → ℂ} {v' : Sp (DualNumber ℂ) ⟶ t.G.left} (ht' : IsTanAtG t x v')
    (hc : IsCombAtG t x v a v') : IsDerivAt0 e (∑ i, a i • w i) v' := by
  refine ⟨ht'.2.trans e0.symm, fun U h f => ?_⟩
  have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => DerLin.le_of_fst_eq ((ht i).2.trans ht'.2.symm) h
  let b : Fin m → TanMod.TanSp x t.G := fun i =>
    TanMod.TanSp.mk (Over.homMk (v i) (ht i).1) (TanMod.smT_zero_of x _ (ht i).2)
  have key : (TanDeriv.evAt v' U h f).snd = ∑ i, a i * (TanDeriv.evAt (v i) U (hU i) f).snd := by
    refine TanDeriv.derivAt_sum b a v' ?_ U h hU f
    obtain ⟨u, hu, rfl⟩ := hc
    have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst hub
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  refine key.trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact congrArg (a i * ·) ((hv i).2 U (hU i) f)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {σ : c.F →+* ℂ}

theorem frame_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := ℂ) (ReciprocityTheory.ChartRestriction.G.Chart.JetR ℂ (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}
    (hx : IsUnivChart _ n xc) (cc : Letter Dw → Fin n → ℂ) (hcc : ∀ z, f.v z.1 z.2 = vec Z.t x xc (cc z)) :
    LinearIndependent ℂ cc ∧ ⊤ ≤ Submodule.span ℂ (Set.range cc) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨p, hp, hps⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hE : ∀ τ m, IsEigV (rho hx) (embK c τ) m ↔ ∀ a : 𝓞 E, vec Z.t x xc m ≫ (Z.t.act.act a).left =
      spMap (epsMul (σ (embK c τ a))) ≫ vec Z.t x xc m := fun τ m => by
    rw [vec_eig_iff hx (fun a => σ (embK c τ a)), ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
    rfl
  have hv : ∀ τ, f.v τ = fun i => vec Z.t x xc (cc ⟨τ, i⟩) := fun τ => funext fun i => hcc ⟨τ, i⟩
  have hb : ∀ τ m, IsEigV (rho hx) (embK c τ) m → ∃! a : Fin (Dw.mult τ) → ℂ, m = ∑ i, a i • cc ⟨τ, i⟩ :=
    fun τ m hm => by
      have := f.basis τ _ (vec_tan hx m) ((hE τ m).1 hm)
      rw [hv] at this
      simpa only [LieLocBasis.comb_iff hx] using this
  have he : ∀ τ (a : Fin (Dw.mult τ) → ℂ), IsEigV (rho hx) (embK c τ) (∑ i, a i • cc ⟨τ, i⟩) := fun τ a r => by
    have h1 : ∀ i, IsEigV (rho hx) (embK c τ) (cc ⟨τ, i⟩) := fun i => (hE _ _).2 (hcc ⟨τ, i⟩ ▸ f.eig τ i)
    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, h1 i r, smul_comm]
  refine ⟨Fintype.linearIndependent_iff.2 fun a ha z => ?_, fun m _ => ?_⟩
  · rw [Fintype.sum_sigma] at ha
    have h1 := proj_sum_eig (rho hx) (embK c) α hinj _ (fun τ => he τ fun i => a ⟨τ, i⟩) z.1
    rw [ha, map_zero] at h1
    exact congrFun ((hb z.1 0 fun r => by simp).unique h1 (y₂ := 0) (by simp)) z.2
  · have h1 := LinearMap.congr_fun (sum_proj (rho hx) (embK c) α hinj) m
    rw [LinearMap.sum_apply, Module.End.one_apply] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := hb τ _ (eig_of_alpha _ _ α hN τ (proj_eig_alpha (rho hx) _ α hinj p hp hps τ m))
    rw [ha]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem dirs_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)}
    (e0 : e 0 = (1 : Over.mk x ⟶ Z.t.G).left) (h1 : ∀ w, ∃! v, IsTanAtG Z.t x v ∧ IsDerivAt0 e w v)
    (h2 : ∀ v, IsTanAtG Z.t x v → ∃! w, IsDerivAt0 e w v) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, IsDerivAt0 e (W z) (f.v z.1 z.2)) : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W := by
  classical
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose cc hcc using fun z : Letter Dw => vec_exists hx _ (f.tan z.1 z.2)
  obtain ⟨hli, hsp⟩ := frame_basis f hx cc hcc
  choose u hu using fun j : Fin n => (h2 _ (vec_tan hx (Pi.single j 1))).exists
  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ u
  have hT : ∀ m, IsDerivAt0 e (T m) (vec Z.t x xc m) := fun m =>
    isDerivAt0_of_comb e0 (fun j => vec_tan hx _) hu (vec_tan hx m) ((LieLocBasis.comb_iff hx _ m m).2 (by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]))
  have hbij : Function.Bijective T := by
    refine ⟨fun m m' h => vec_inj hx ((h1 (T m)).unique ⟨vec_tan hx m, hT m⟩ ⟨vec_tan hx m', h ▸ hT m'⟩), fun w => ?_⟩
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h1 w
    obtain ⟨m, rfl⟩ := vec_exists hx v hv
    exact ⟨m, (h2 _ hv).unique (hT m) hd⟩
  refine ⟨(Module.Basis.mk hli hsp).map (LinearEquiv.ofBijective T hbij), funext fun z => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  exact (h2 _ (f.tan z.1 z.2)).unique (hcc z ▸ hT (cc z)) (hW z)

theorem differentiableAt_dir {n g : ℕ} {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (he : IsExpChart e ex) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {B : Set V} (hB : IsOpen B) {x : V → CxPts (genStr Z) σ}
    (hx : IsHolTo B fun b => (x b).1) (hs : ∀ b ∈ B, x b ∈ e.source) {v : V → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)}
    (hv : HolTan B v) {W : V → Fin g → ℂ} (hW : ∀ b ∈ B, IsDerivAt0 (fun w => (ex (x b) w).left) (W b) (v b))
    {b₀ : V} (hb₀ : b₀ ∈ B) : DifferentiableAt ℂ W b₀ := by
  obtain ⟨-, h1, -, h3, h4, h5⟩ := he
  let ε : CxPts (genStr Z) σ → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun y w => (ex y w).left
  have hz : DifferentiableAt ℂ (fun b => e (x b)) b₀ :=
    differentiableAt_pi.2 fun k => (h1 k V B x hB hx hs).differentiableAt (hB.mem_nhds hb₀)
  have ht := e.map_source (hs b₀ hb₀)
  have hl : ∀ b ∈ B, ε (e.symm (e (x b))) = ε (x b) := fun b hb => by rw [e.left_inv (hs b hb)]
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (U : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, U)), ⊤ ≤ ε (x b₀) 0 ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (ε (x b₀) z) U f) 0 w = 0 := by
    intro U f hU
    have hU' : ⊤ ≤ ε (e.symm (e (x b₀))) 0 ⁻¹ᵁ U := by rwa [hl b₀ hb₀]
    have d := (HolLieFrame.differentiableAt_fderiv (e := fun z => ε (e.symm z)) h4 ht U f hU').comp b₀ hz
    have hn : ∀ᶠ b in 𝓝 b₀, b ∈ B ∧ ⊤ ≤ v b ⁻¹ᵁ U := by
      have hc : ContinuousAt (fun b => (e (x b), (0 : Fin g → ℂ))) b₀ := hz.continuousAt.prodMk continuousAt_const
      filter_upwards [hB.mem_nhds hb₀, hc.preimage_mem_nhds ((h4 U f).1.mem_nhds ⟨⟨ht, trivial⟩, hU'⟩)] with b hb hb'
      have h' : ⊤ ≤ ε (e.symm (e (x b))) 0 ⁻¹ᵁ U := hb'.2
      rw [hl b hb] at h'
      exact ⟨hb, (TangentOrigin.top_le_preimage_iff _ U).2 (by rw [(hW b hb).1]; exact h')⟩
    refine hw (fun b => fderiv ℂ (fun z => valAt' (ε (x b) z) U f) 0) (d.congr_of_eventuallyEq ?_)
      (((hv U f).differentiableAt hn).congr_of_eventuallyEq ?_)
    · filter_upwards [hB.mem_nhds hb₀] with b hb
      simp only [Function.comp_apply, hl b hb]
    · filter_upwards [hn] with b ⟨hb, h⟩
      refine ((hW b hb).2 U h f).symm.trans ?_
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR, dif_pos h]
  have d₁ := LocalLift.isDerivAt0_const (ε (x b₀)) w hw'
  have d₀ := LocalLift.isDerivAt0_const (ε (x b₀)) 0 fun _ _ _ => map_zero _
  have e0 : ex (x b₀) 0 = 1 := by simpa using h3 _ (hs b₀ hb₀) 0 0
  exact ((h5 _ (hs b₀ hb₀)).2 _ ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (ex (x b₀) 0))),
    d₁.1.trans (congrArg (·.left) e0)⟩).unique d₁ d₀

theorem exists_inverse {J : Type} [Fintype J] [DecidableEq J] {g : ℕ} (b : Module.Basis J ℂ (Fin g → ℂ)) :
    ∃ Wi : Matrix (Fin g) J ℂ, Matrix.of b * Wi = 1 ∧ Wi * Matrix.of b = 1 := by
  refine ⟨Matrix.of fun j z => b.repr (Pi.single j 1) z, ?_, ?_⟩
  · ext z z'
    have h : b z = ∑ j, b z j • (Pi.single j 1 : Fin g → ℂ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 := congrArg (fun w => b.repr w z') h
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.finset_sum_apply,
      Finsupp.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_apply, Matrix.one_apply, h2]
    rfl
  · ext j k
    have h := congrFun (b.sum_repr (Pi.single j 1)) k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Finset.sum_apply, Pi.single_apply, eq_comm] using h

theorem exists_dirs_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ e.source) → ∃ (W : V → Matrix (Letter Dw) (Fin g) ℂ) (Wi : V → Matrix (Fin g) (Letter Dw) ℂ), ContinuousOn W B ∧ ContinuousOn Wi B ∧ ∀ b ∈ B, Dirs (a b) (fun w => (ex (a b).1 w).left) (W b) ∧ W b * Wi b = 1 ∧ Wi b * W b = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex he V _ _ _ B a hB ha hs
  have h5 := fun b hb => he.2.2.2.2.2 _ (hs b hb)
  choose! W hW using fun b hb (z : Letter Dw) => ((h5 b hb).2 _ ((a b).2.tan z.1 z.2)).exists
  have hbas : ∀ b ∈ B, ∃ bs : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑bs = W b := fun b hb => by
    have e0 : ex (a b).1 0 = 1 := by simpa using he.2.2.2.1 _ (hs b hb) 0 0
    exact dirs_basis (a b).2 (e := fun w => (ex (a b).1 w).left) (congrArg (·.left) e0) (h5 b hb).1 (h5 b hb).2 (hW b hb)
  have hinv : ∀ b ∈ B, ∃ Wi : Matrix (Fin g) (Letter Dw) ℂ, Matrix.of (W b) * Wi = 1 ∧ Wi * Matrix.of (W b) = 1 :=
    fun b hb => by
      obtain ⟨bs, h⟩ := hbas b hb
      rw [← h]
      exact exists_inverse bs
  choose! Wi hWi using hinv
  have hd : ∀ b ∈ B, ∀ z, DifferentiableAt ℂ (fun b => W b z) b := fun b hb z =>
    differentiableAt_dir he hB ha.1 hs (ha.2 z.1 z.2) (fun b hb => hW b hb z) hb
  refine ⟨fun b => Matrix.of (W b), Wi, fun b hb => ContinuousAt.continuousWithinAt ?_,
    fun b hb => ContinuousAt.continuousWithinAt ?_, fun b hb => ⟨hW b hb, hWi b hb⟩⟩
  · exact continuousAt_pi.2 fun z => (hd b hb z).continuousAt
  · obtain ⟨bs, -⟩ := hbas b hb
    let q : Fin g ≃ Letter Dw := (Pi.basisFun ℂ (Fin g)).indexEquiv bs
    refine continuousAt_pi.2 fun j => continuousAt_pi.2 fun z => ?_
    have := HolFrameMatrix.differentiableAt_of_mul_eq_one (fun b => (Wi b).submatrix id q)
      (fun b => (Matrix.of (W b)).submatrix q id) b (fun i k => differentiableAt_pi.1 (hd b hb (q i)) k) (by
        filter_upwards [hB.mem_nhds hb] with b' hb'
        rw [Matrix.submatrix_mul_equiv, (hWi b' hb').2]
        rfl) j (q.symm z)
    simpa using this.continuousAt

end GlobalTheory.ShFam.Hor.ExpDirs
