import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

def PsiTied {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (hk : R.k = n)
    {LL O Kf : Type} [Field LL] [CommRing O] [Field Kf] [Algebra O Kf] (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) : Prop :=
  ∀ (a : Formalism.L2.Herm.awayFrom₂ L p) (κ : S.U),
    (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) →
    (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
      bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) (reGL hk _ a.1)) →
    ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap O Kf ((ψ a : Oˣ) : O) * e r = 1

end Gen

variable {D : D7} (X : Formalism.L2.Herm.Herm0 D)

set_option maxHeartbeats 4000000 in

theorem chi_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E)
    (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (hL : X.lev0 u = L)
    (ψ : Formalism.L2.Herm.awayFrom₂ L (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ)
    (hχ : ∀ i (γ : ((D.gat u w hg).lev i).Γ) (a : Formalism.L2.Herm.awayFrom₂ L (D.what₂.places.resChar w)),
      a.1 = (((X.g u w hg).yG i).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
        ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1 → ((D.gat u w hg).lev i).χ γ = ψ a)
    (hψ : PsiTied ((T u).cls0).lev L (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL e ψ)
    (i : (D.gat u w hg).comp) (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U)
    (hκ : (locAt X u w hg B).IsAway i γ κ.1) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * e r = 1 := by
  subst hL
  have h1 : (((X.g u w hg).yG i).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1 ∈ Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w) :=
    (mem_map_conj _ _ _).1 (((X.g u w hg).gamI_range i _).1 ⟨γ, rfl⟩)
  have ee : ((locAt X u w hg B).yG i)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((locAt X u w hg B).gamI i γ) * (locAt X u w hg B).yG i = reGL (rank_eq_first_level D.R) _ ((((X.g u w hg).yG i).1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1) := by
    rw [map_mul, map_mul, map_inv, ← bc_reGL]
    rfl
  rw [hχ i γ ⟨_, h1⟩ rfl]
  refine hψ ⟨_, h1⟩ κ (fun v hv => ?_) (fun w' hw' => ?_)
  · obtain ⟨v', rfl⟩ := LocGood.exists_pl (locAt X u w hg B) v hv
    exact hκ.1 v'
  · rw [hκ.2 w' hw', ee]

end Formalism.L2.G
