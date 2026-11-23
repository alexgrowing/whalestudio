import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

def chartPullPerm {X Y Y' : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ' : K' → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε' : K' → ℤ) (ε : K → ℤ) (h : Y' ⟶ Y) (e : K' ≃ K)
    (hc : ∀ k, φ' (e.symm k) = h ≫ φ k) (hε : ∀ k, ε' (e.symm k) = ε k) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) h :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j (e.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy (e.symm k)
      rw [hc] at this
      exact this
  { idx := fun j k => j (e.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (Fintype.prod_equiv e.symm _ _ fun k => ?_).symm
      rw [Category.id_comp, hc, hε] }

theorem psum_perm {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (I : Finset (Fin n)) : psum G x' I = h ≫ psum G x (I.map σ.toEmbedding) := by
  rw [CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => hx i

def chartPullCube {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (L : LB G.left) : ChartPull (cubeLB G x' L) (cubeLB G x L) h.left :=
  chartPullPerm L _ _ _ _ h.left (Equiv.ulift.trans ((Equiv.finsetCongr σ).trans Equiv.ulift.symm))
    (fun k => by
      show (psum G x' ((Equiv.finsetCongr σ).symm k.down)).left = h.left ≫ (psum G x k.down).left
      rw [psum_perm G h x x' σ hx, Over.comp_left]
      congr 3
      exact (Equiv.finsetCongr σ).apply_symm_apply k.down)
    (fun k => by
      show (-1 : ℤ) ^ (n - ((Equiv.finsetCongr σ).symm k.down).card) = (-1) ^ (n - k.down.card)
      simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply])

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_swap {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} (H : GAdj L₁ L₂ u u') : GAdj L₂ L₁ u' u :=
  LBIso.chartPull
    (chartPullCube G₁ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂, snd G₁ G₂ ≫ u'] ![fst G₂ G₁ ≫ u', snd G₂ G₁]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₁)
    (chartPullCube G₂ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂ ≫ u, snd G₁ G₂] ![fst G₂ G₁, snd G₂ G₁ ≫ u]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₂)
    (LBIso.symm H)

theorem gAdj_comp {S : Scheme.{0}} {G₁ G₂ G₃ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    [GrpObj G₃] [IsCommMonObj G₃] {L₁ : LB G₁.left} {L₂ : LB G₂.left} {L₃ : LB G₃.left} (hL₁ : L₁.IsLB)
    (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} {v : G₂ ⟶ G₃} {v' : G₃ ⟶ G₂}
    (H : GAdj L₁ L₂ u u') (H' : GAdj L₂ L₃ v v') : GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  LBIso.trans (LB.isLB_linComb hL₃ _ _) (LB.isLB_linComb hL₂ _ _) (LB.isLB_linComb hL₁ _ _)
    (LBIso.chartPull
      (chartPullCube G₃ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃ ≫ v, snd G₂ G₃]
        ![fst G₁ G₃ ≫ u ≫ v, snd G₁ G₃] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₃)
      (chartPullCube G₂ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃, snd G₂ G₃ ≫ v']
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂) H')
    (LBIso.chartPull
      (chartPullCube G₂ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂ ≫ u, snd G₁ G₂]
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂)
      (chartPullCube G₁ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂, snd G₁ G₂ ≫ u']
        ![fst G₁ G₃, snd G₁ G₃ ≫ v' ≫ u'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₁) H)

theorem gAdj_swap_comp :
    (∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : LB G₁.left)
      (L₂ : LB G₂.left), L₁.IsLB → L₂.IsLB → ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), GAdj L₁ L₂ u u' → GAdj L₂ L₁ u' u) ∧
    ∀ (S : Scheme.{0}) (G₁ G₂ G₃ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃]
      [IsCommMonObj G₃] (L₁ : LB G₁.left) (L₂ : LB G₂.left) (L₃ : LB G₃.left), L₁.IsLB → L₂.IsLB → L₃.IsLB →
      ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) (v : G₂ ⟶ G₃) (v' : G₃ ⟶ G₂), GAdj L₁ L₂ u u' → GAdj L₂ L₃ v v' →
        GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ H => gAdj_swap H,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ _ _ _ _ H H' => gAdj_comp h₁ h₂ h₃ H H'⟩

end GlobalTheory.MumFam
