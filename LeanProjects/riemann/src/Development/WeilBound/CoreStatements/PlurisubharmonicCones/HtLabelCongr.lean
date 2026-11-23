import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ProdSqrtLead
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubset
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Lat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

theorem patch_congr' (T : Finset ℕ) (L₀ : Lat ξ V) (Lp Lp' : ℕ → Lat ξ V)
    (h : ∀ p ∈ T, ∀ q, InFibre ξ p q → Lp p q = Lp' p q) : Lat.patch T L₀ Lp = Lat.patch T L₀ Lp' := by
  funext q
  simp only [Lat.patch]
  split_ifs with hF
  · refine iInf_congr fun p => iInf_congr fun hp => iInf_congr fun hq => ?_
    rw [h p hp q hq]
  · rfl

theorem vbOn_congr {L L' : Lat ξ V} {T : Set (Cpt ξ)} {r : ℕ} {U : Submodule Ω V} (h : ∀ q ∈ T, L q = L' q)
    (hL : L.IsVBOn T r U) : L'.IsVBOn T r U := by
  intro p hp
  obtain ⟨W, hW, b, hb, hf⟩ := hL p hp
  exact ⟨W, hW, b, hb, fun q hq hqW => ⟨(hf q hq hqW).1, (h q hq).symm.trans (hf q hq hqW).2⟩⟩

end Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem htLabel_congr {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) {n n' : ℕ}
    (ρ : 𝓞 E →+* Module.End Ω Li) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) (s : CMType H ⊕ CMType H) {q : Cpt ξ}
    (h : M.htOm L n q = M.htOm L n' q) : htLabel M L n ρ σ s q = htLabel M L n' ρ σ s q := by
  rcases s with τ | τ
  · simp only [htLabel, LieModel.htW, LieModel.htDual, h]
  · simp only [htLabel, LieModel.htDual, h]

section Level

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S₀ y) (S : Finset ℕ)

theorem patch_four (h : ∀ p ∈ S, ∀ q, InFibre 𝔐.ξ p q → 𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q)
    (s : CMType H ⊕ CMType H) :
    Lat.patch S (𝔐.dR s) (fun p => htLabel 𝔐.M 𝔐.t.PP.L (p ^ 4) 𝔐.ρ 𝔐.emb s) = 𝔐.VS S s :=
  patch_congr' _ _ _ _ fun p hp q hq => htLabel_congr _ _ _ _ _ (h p hp q hq)

def levFour (hp : ∀ p ∈ S, p.Prime) (hR : ∀ p ∈ S, 4 ≤ 𝔐.R p) (ht : ∀ p ∈ S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p))
    (hvb : ∀ s, (𝔐.VS S s).IsVB (labelRk D s) (𝔐.Vgen s))
    (h : ∀ p ∈ S, ∀ q, InFibre 𝔐.ξ p q → 𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q) :
    HodgeCpt Y S y :=
  { 𝔐 with
    S_prime := hp
    R := fun _ => 4
    R_ge := fun _ _ => le_rfl
    tors := fun p hpS k _ i g hg => ht p hpS k i g (by
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (hR p hpS)
      rw [hn, pow_add, pow_mul, hg, _root_.one_pow])
    vb := fun s => by
      have h1 := hvb s
      rw [← patch_four 𝔐 S h s] at h1
      exact h1 }

end Level

theorem pull_on {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω'] {i : Ω →+* Ω'}
    {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)]
    {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'} (B : HodgeCpt Y S y) (A : HodgeCpt Y S y') (g : A.X ⟶ B.X)
    (x : Sp Ω ⟶ Xo.XF c) (hx : B.ξ ≫ B.f = x ≫ Y.j) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((B.M.htOm B.t.PP.L (p ^ B.R p)).map (B.Vgen s).dualRestrict).IsVBOn {q | InFibre B.ξ p q}
      (labelRk D s) ⊤)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ B.ξ g i) (hf : g ≫ B.f = A.f) (hR : ∀ p ∈ S, A.R p = B.R p) :
    ∃ (j : B.Li →+ A.Li) (m : SABMap A.t B.t g), IsExtOver i j ∧
      (∀ a, (A.M.pt (j a)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (B.M.pt a).left) ∧
      ∀ s, A.V s = (B.V s).pull A.ξ g j := by
  obtain ⟨A', e, j', m', p1, p2, p3, p4, p5, p6, p7, -, p9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S Ω Ω' i K K' J J' y y' B x A.X A.ξ g hx hdisc hvb A.all A.tie A.normal hd
  have he : A.ξ ≫ e.symm.hom = A'.ξ := by
    rw [← p1]
    simp
  have hf' : e.symm.hom ≫ A'.f = A.f := by
    rw [p2, ← hf]
    simp
  have hc : A'.cst = A.cst := by
    refine OrLinked.ringHom_ext_int c (OrLinked.spMap_inj' ?_)
    rw [← A'.cst_over, ← A.cst_over, ← hf', ← he]
    simp only [Category.assoc]
  obtain ⟨φ, φt, -, φr, φp⟩ := OrLinked.same_base_cmp A' A e.symm he hf' hc
  have ha : (FrameRebase.sabRebase A.m hf.symm).φ = A.m.φ := FrameRebase.sabRebase_φ _ _
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t B.t A.t B.f g B.m (FrameRebase.sabRebase A.m hf.symm)
  rw [ha] at hk
  let j : B.Li →+ A.Li := φ.toLinearMap.toAddMonoidHom.comp j'
  have hjd : ∀ a, j a = φ (j' a) := fun _ => rfl
  have hj : IsExtOver i j := ⟨fun a v => by rw [hjd, hjd, p6.1, map_smul], fun n b hb =>
    (p6.2 n b hb).map' φ.toLinearMap φ.ker⟩
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ B.ξ (e.hom ≫ g) i := by
    show A'.ξ ≫ e.hom ≫ g = _
    rw [← Category.assoc, p1]
    exact hd
  refine ⟨j, k, hj, fun a => B.m.cart.1.hom_ext ?_ ?_, fun s => ?_⟩
  · show ((A.M.pt (φ (j' a))).left ≫ k.φ) ≫ B.m.φ = _
    rw [Category.assoc, ← hk, φt, p3, ← Category.assoc, p7]
  · have w1 := Over.w (A'.M.pt (j' a))
    have w2 := Over.w (A.M.pt (φ (j' a)))
    have w3 : (A'.M.pt (j' a)).left ≫ A'.t.G.hom ≫ e.hom = (A.M.pt (φ (j' a))).left ≫ A.t.G.hom := by
      rw [← Category.assoc, w1, w2, ← p1]
      exact Category.assoc _ _ _
    show ((A.M.pt (φ (j' a))).left ≫ k.φ) ≫ B.t.G.hom = _
    rw [← p7, Category.assoc, Category.assoc, k.cart.1.w, m'.cart.1.w, ← Category.assoc, ← w3]
    simp only [Category.assoc]
  · funext q
    obtain ⟨hq, -, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ g i hd q
    obtain ⟨U, hU, b, -, hb⟩ := B.vb s ⟨g q.1, hq⟩ trivial
    have hb1 : (B.V s).IsFrameAt b ⟨g q.1, hq⟩ := hb _ trivial hU
    have h' := OrLinked.genPt_spec e.symm he q
    have e1 : (e.hom ≫ g) (e.symm.hom q.1) = g q.1 := by simp
    have hq' : genPt B.ξ ⤳ (e.hom ≫ g) (e.symm.hom q.1) := e1 ▸ hq
    have hb2 : (B.V s).IsFrameAt b ⟨(e.hom ≫ g) (e.symm.hom q.1), hq'⟩ := by
      have : (⟨(e.hom ≫ g) (e.symm.hom q.1), hq'⟩ : Cpt B.ξ) = ⟨g q.1, hq⟩ := Subtype.ext e1
      rw [this]
      exact hb1
    have hb3 := FlagPull.pull_isFrameAt hd' p6 ⟨e.symm.hom q.1, h'⟩ hq' hb2
    rw [← p9] at hb3
    have hb4 : (A.V s).IsFrameAt (fun k => φ (j' (b k))) q :=
      OrLinked.frame_tr φ (φr q h') (φp S (fun p hp => by rw [p5]; exact hR p hp) s q h') hb3
    exact hb4.2.trans (FlagPull.pull_isFrameAt hd hj q hq hb1).2.symm

end LevelTowerAlt.Comparison₂
