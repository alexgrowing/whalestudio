import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.LocM.MapComp GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

namespace GlobalTheory.LocM.LatCover

theorem exists_frame_of_rows : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (a : ∀ σ : E →+* ℂ, Fin (Dw.mult σ + 1) → GL (Fin n) Γ(Z.X, U)), (∀ σ (r : Fin (Dw.mult σ + 1)), LatCover.StepAt Z B g L σ r hU m (a σ r)) → ∀ (c : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, U)), (∀ σ, ∃ (M : GL (Fin n) Γ(Z.X, U)) (e : Fin (Dw.mult σ) ↪ Fin n), ∀ i l, M (e i) l = c σ i l) → (∀ σ (i : Fin (Dw.mult σ)), ∃ j : Fin n, (j : ℕ) < i + 1 ∧ ∀ l, c σ i l = ((a σ i.succ)⁻¹ : GL (Fin n) Γ(Z.X, U)) l j) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X), ⊤ ≤ x ⁻¹ᵁ U → Set.range x ⊆ Z.opn → ∃ u, Z.FlagAt x u ∧ HasCoord g L m x u fun σ i l => valR x U (c σ i l) := by
  intro hΦ E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg U hU V hUV n m hm a hst c hext hrow k _ x hxU hxo
  classical
  obtain ⟨φx, hφ, hval⟩ : ∃ φ : Γ(Z.X, U) →+* k, spMap φ ≫ hU.fromSpec = x ∧ ∀ f, valR x U f = φ f :=
    ⟨_, GlobalTheory.FlagMod.spMap_ev x hU hxU, fun f => by rw [valR, dif_pos hxU]; rfl⟩
  obtain ⟨τ, mu, htr, hπ⟩ := StepBasis.exists_isTrans hg (x (IsLocalRing.closedPoint k))
  have h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V := GlobalTheory.FlagMod.le_preimage_map g hUV hxU
  obtain ⟨Φ, hΦw⟩ := hΦ E H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k x h hxo τ mu hπ
  obtain ⟨a0, ψ0, h0⟩ := Z.exists_chart x hxo
  have fu0 := CommonMod.flagAt_chart Z h0
  have fu0' := fu0
  set u0 := (Z.fr a0).bc ψ0 with hu0
  obtain ⟨b, χ, hb, fr, sf⟩ := fu0

  let w : Vecs Dw (Y Z.i).t k := fun σ i => (tv (Φ.symm fun l => φx (c σ i l))).left
  have hwT : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (w σ i) := fun σ i => GlobalTheory.LieMet.isTan_tv _

  have hco : HasCoord g L m x w fun σ i l => valR x U (c σ i l) := by
    refine ⟨τ, mu, h, htr, fun σ i => ?_⟩
    obtain ⟨v, hv, e1, e2⟩ := hΦw (Φ.symm fun l => φx (c σ i l))
    exact ⟨v, hv, e1, fun l => by rw [e2, LinearEquiv.apply_symm_apply]; exact (hval _).symm⟩

  have hB : ∀ σ, ∃ (n' : ℕ) (v : Fin n' → (Sp (DualNumber k) ⟶ (Y Z.i).t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n'),
      (∀ i, v (e i) = w σ i) ∧ StepFrame.Bas (Y Z.i).t (x ≫ Z.π) v := by
    intro σ
    obtain ⟨M, e, hM⟩ := hext σ
    refine ⟨n, fun j => (tv (Φ.symm fun l => φx (M j l))).left, e, fun i => ?_, ?_⟩
    · show (tv (Φ.symm fun l => φx (M (e i) l))).left = (tv (Φ.symm fun l => φx (c σ i l))).left
      simp only [hM]
    · rw [StepFrame.bas_iff_full (fun j => GlobalTheory.LieMet.isTan_tv _)]
      have ee : (fun j => GlobalTheory.LieMet.tanOf (GlobalTheory.LieMet.isTan_tv (Φ.symm fun l => φx (M j l)))) =
          fun j => Φ.symm fun l => φx (M j l) := funext fun j => GlobalTheory.LieMet.tan_ext rfl
      rw [ee]
      have hli : LinearIndependent k fun j => Φ.symm fun l => φx (M j l) := by
        have hu : IsUnit (((M : Matrix (Fin n) (Fin n) Γ(Z.X, U))).map φx) :=
          (Matrix.GeneralLinearGroup.map φx M).isUnit
        exact (Matrix.linearIndependent_rows_of_isUnit hu).map' Φ.symm.toLinearMap Φ.symm.ker
      have : Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G) := Module.Finite.equiv Φ.symm
      refine (StepFrame.uniq_iff _).2 ⟨hli, hli.span_eq_top_of_card_eq_finrank' ?_⟩
      rw [LinearEquiv.finrank_eq Φ, Module.finrank_fin_fun, Fintype.card_fin]

  have hW : ∀ σ (i : Fin (Dw.mult σ)), ∃ cf : Fin (Dw.mult σ) → k,
      (∀ j : Fin (Dw.mult σ), (i : ℕ) + 1 ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z.i).t (x ≫ Z.π) (u0 σ) cf (w σ i) := by
    intro σ i
    obtain ⟨j0, hj0, hcj⟩ := hrow σ i
    let A := a σ i.succ
    let col : Fin n → (Sp (DualNumber k) ⟶ (Y Z.i).t.G.left) := fun j =>
      (tv (Φ.symm fun l => φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j))).left
    have hst' := hst σ i.succ k φx
    rw [hφ] at hst'
    have hstep : ∀ i' : Fin (Dw.mult σ), (i' : ℕ) < (i : ℕ) + 1 → ∃ cf : Fin n → k,
        (∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z.i).t (x ≫ Z.π) col cf (u0 σ i') := by
      intro i' hi'
      let w' := GlobalTheory.LieMet.tanOf (fr.1 σ i').1
      obtain ⟨v, hv, e1, e2⟩ := hΦw w'
      have hz := hst' v hv h ⟨τ, mu, u0, i', htr, fu0', by simpa using hi', e1⟩
      refine ⟨fun j => ∑ l, φx (A j l) * Φ w' l, fun j hj => ?_, ?_⟩
      · have := hz j (by simpa using hj)
        simpa only [e2] using this
      · refine (GlobalTheory.LieMet.isComb_iff (fun j => Φ.symm fun l => φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j)) _ w').2 ?_
        apply Φ.injective
        rw [map_sum]
        simp only [map_smul, LinearEquiv.apply_symm_apply]
        funext l
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have hI : ((A⁻¹ : GL (Fin n) Γ(Z.X, U)) : Matrix (Fin n) (Fin n) Γ(Z.X, U)) * (A : Matrix (Fin n) (Fin n) Γ(Z.X, U)) = 1 :=
          Units.inv_mul A
        have hinv : ∀ l', ∑ j, φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j) * φx (A j l') = if l = l' then 1 else 0 := by
          intro l'
          have := congrArg φx (congrFun (congrFun hI l) l')
          rw [Matrix.mul_apply, map_sum] at this
          simp only [map_mul] at this
          rw [this, Matrix.one_apply]
          split_ifs <;> simp
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ l', ∑ j, φx (A j l') * Φ w' l' * φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j) =
            (if l = l' then 1 else 0) * Φ w' l' := fun l' => by
          rw [← hinv l', Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hr : (i : ℕ) + 1 ≤ Dw.mult σ := i.2
    obtain ⟨-, hsp⟩ := StepFrame.step_eq fr hr (fun j => GlobalTheory.LieMet.isTan_tv _) hstep
    obtain ⟨cf, hcf, hcomb⟩ := hsp j0 hj0
    refine ⟨cf, hcf, ?_⟩
    have ew : w σ i = col j0 := by
      show (tv (Φ.symm fun l => φx (c σ i l))).left = _
      simp only [hcj]
      rfl
    rw [ew]
    exact hcomb
  have key := StepFrame.isFrame_of_steps fr Z.ty hW hB
  exact ⟨w, ⟨b, χ, hb, key.1, sameFlag_trans (tan_chart Z hb) (fun σ j => (fr.1 σ j).1) (fun σ j => (key.1.1 σ j).1)
    sf key.2⟩, hco⟩

end GlobalTheory.LocM.LatCover
