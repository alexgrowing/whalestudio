import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

def GlobalDatumCompatibility (D : D7) : Prop :=
  Formalism.MainNotions.SphericalInertData.HypEFK D ∧
    (2 ≤ Module.finrank ℚ D.host.F ∧
      ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) ∧
    ∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)

theorem nV_pos (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.t_odd.pos
  show 1 ≤ D.R.r + D.R.t
  omega

theorem hypCM_of (D : D7) (hc : GlobalDatumCompatibility D) : Formalism.MainNotions.SphericalInertData.HypCM D := by
  refine ⟨?_, hc.2.1⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem base_change_automorphic_of (D : D7) (h45 : Formalism.MainNotions.SphericalInertData.Conclusion1 D) (hc : GlobalDatumCompatibility D) :
    Formalism.MainNotions.SumRepresentations.adm1 D := by
  intro i P
  obtain ⟨Pa, h1, h2, h3, h4, h5, h6⟩ :=
    h45 hc.1 (hypCM_of D hc) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (nV_pos D)
      (hc.2.2 _ (D.nd.j_range i).1 (D.nd.j_range i).2) (D.nbc.embAV i P)
      (fun w hw => D.nbc.embAV_sph i P w hw)
  refine ⟨Pa, h1, h2, h3, fun w hw => (h4 w hw).trans (D.nbc.embAV_loc i P w).symm,
    fun w hw => ⟨(h5 w hw).1, (h5 w hw).2.trans (congrArg _ (D.nbc.embAV_sat i P w).symm)⟩,
    fun τ => (h6 τ).trans (congrFun (D.nbc.embAV_inf i P) τ).symm⟩

def LitBNIrr (Γ : Type) [Group Γ] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)),
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly) →
    Formalism.CyclotomicNorms.IrredOn ρ' ⊤ → Formalism.CyclotomicNorms.IrredOn ρ ⊤

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B).charpoly =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).charpoly).map f :=
  Matrix.charpoly_map _ f

theorem irredOn_fbCast {Γ : Type} [Group Γ] {p q : ℕ} (h : p = q) (hp : p.Prime) (hq : q.Prime) {a : ℕ}
    (ρ : Γ →* GL (Fin a) (Fb p hp))
    (hρ : @Formalism.CyclotomicNorms.IrredOn a p ⟨hp⟩ Γ _ ρ ⊤) :
    @Formalism.CyclotomicNorms.IrredOn a q ⟨hq⟩ Γ _ (mapRep (fbCast h hp hq).toRingHom ρ) ⊤ := by
  subst h
  have e : mapRep (fbCast rfl hp hq).toRingHom ρ = ρ := by
    ext g i j
    rfl
  rw [e]
  exact hρ

def GlobalDatumRegularity (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (u : (ZMod (D.host.g k))ˣ) (y : D.nd.O i),
    D.nd.l i ≠ D.host.g k →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.naut.iotaQC i (D.naut.iotaQ i (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) y)) =
      D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))) →
    D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y) =
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i))
          (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))))

theorem irreducibility_of_theorem_three (D : D7) (h33 : Formalism.MainNotions.ArithmeticCylinders.PointsLemma D) (hBN : LitBNIrr (G D.host.E D.nd.Om))
    (hc : GlobalDatumRegularity D) : Formalism.MainNotions.SumRepresentations.At.IrreducibilityParameter D.nd D.naut := by
  intro i σ _ hgood Sig hSig ρ hρ
  obtain ⟨-, hw⟩ := h33 D.ntypes.BB_disj σ hgood (fun k v => (D.ntypes.tg_gen k v).2)
  obtain ⟨hirr, -, hroot⟩ := hw (D.nd.w i)
  obtain ⟨-, hcp⟩ := D.rbar_tie i σ Sig ρ hSig hρ
  refine ⟨?_, ?_⟩
  · refine hBN (D.nd.l i) D.R.r _ _ (fun g => ?_)
      (irredOn_fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out _ hirr)
    rw [charpoly_mapRep, charpoly_mapRep]
    exact (hcp g).symm
  · intro k hk v _ hr
    rw [D.ntypes.heckeLoc_gamma_places i k v] at hr
    have hk' : D.what₂.places.resChar (D.nd.w i) ≠ D.host.g k := by rw [D.nd.w_l i]; exact hk
    rw [charpoly_mapRep, ← hcp] at hr
    have hχ : chi1 D.nd i (D.ntypes.tg k v) =
        ((D.nd.chi i 1 (D.ntypes.tg k v) : (D.nd.O i)ˣ) : D.nd.O i) := rfl
    rcases D.ntypes.chiT_tg i k v hk with h | h
    · rw [hχ, hc i k v _ _ hk h] at hr
      exact hroot k hk' v _ _ (Or.inl rfl) (hr.of_map (RingEquiv.injective _))
    · rw [hχ, hc i k v _ _ hk h] at hr
      exact hroot k hk' v _ _ (Or.inr rfl) (hr.of_map (RingEquiv.injective _))

end Formalism.MainNotions.N
