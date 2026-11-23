import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.CastGLApply
import Formalism.LocalToGlobal.HermitianColumns.CompletionIntegersIff

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

structure LocId (L : ColLevel R F E sp gp C A clsLat) (p nV : ℕ) (W Qq : Type) [CommRing W] [Field Qq] [Algebra W Qq] where
  pl : Fin nV ≃ {v : HeightOneSpectrum (𝓞 F) // ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}
  eQ : ∀ v : Fin nV, Qq ≃+* (pl v).1.adicCompletion F
  completion_integers_iff : ∀ v (x : Qq), x ∈ Set.range (algebraMap W Qq) ↔ eQ v x ∈ (pl v).1.adicCompletionIntegers F
  spl : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F
  spl_sig : ∀ w h x, spl w h (sigR sp.cm.sig (w.adicCompletion F) x) = swapR _ (spl w h x)
  spl_alg : ∀ w h (a : w.adicCompletion F), spl w h ((1 : E) ⊗ₜ[F] a) = (a, a)
  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin R.k) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin R.k → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w L.Lb, ∀ a, (spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin R.k) (w.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

namespace LocId

variable {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
  (I : LocId L p nV W Qq)

def iw (v : Fin nV) : E →+* Qq :=
  (I.eQ v).symm.toRingHom.comp ((RingHom.fst _ _).comp ((I.spl (I.pl v).1 (I.pl v).2).toRingHom.comp
    (inclE (F := F) ((I.pl v).1.adicCompletion F))))

def frQ (v : Fin nV) : GL (Fin R.k) Qq := bc (I.eQ v).symm.toRingHom (I.fr (I.pl v).1 (I.pl v).2)

end LocId

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

abbrev compL (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : Type :=
  compC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p)

abbrev gatOfLevel (L : ColLevel R F E sp gp C A clsLat) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ) : GAtP p :=
  gatConst sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ (fun i => (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F))) e

set_option maxHeartbeats 2000000 in

def gatOfLevel_tie (L : ColLevel R F E sp gp C A clsLat) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (hy : ∀ i, (Quotient.mk'' (y i) : compL L p) = i)
    (hyp : ∀ i (w' : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w'.asIdeal →
      bc (prV (E := E) w') (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) :
    Formalism.L2.Herm.GLevTie L (gatOfLevel L hS nV r lam0 dom hk I ψ y e) where
  rk := hk
  pl := I.pl
  eQ := fun v w' h => h ▸ I.eQ v
  completion_integers_iff := by
    intro v w' h x
    subst h
    exact I.completion_integers_iff v x
  spl := I.spl
  spl_sig := I.spl_sig
  spl_alg := I.spl_alg
  fr := I.fr
  fr_lat := I.fr_lat
  yG := y
  yG_p := hyp
  yG_bij := ⟨fun a b hab => by
      have h1 := hy a; have h2 := hy b
      simp only at hab
      rw [← h1, ← h2]; exact hab, fun i => ⟨i, hy i⟩⟩
  gamI := fun i => (gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F))).subtype
  gamI_inj := fun i => Subtype.val_injective
  gamI_range := by
    intro i γ
    constructor
    · rintro ⟨g, rfl⟩
      exact g.2
    · intro h
      exact ⟨⟨γ, h⟩, rfl⟩
  act_eq := by
    intro i v w' h hw γ a b a' b' ha hb
    subst h
    have h1 := levC_act sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ
      (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) v γ
    have h2 : (((gatOfLevel L hS nV r lam0 dom hk I ψ y e).lev i).act v γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b =
        (castGL hk Qq (((gatOfLevel L hS nV r lam0 dom hk I ψ y e).lev i).act v γ) :
          Matrix (Fin R.k) (Fin R.k) Qq) a' b' := by
      rw [castGL_apply]
      have ea : a = Fin.cast hk.symm a' := Fin.ext ha
      have eb : b = Fin.cast hk.symm b' := Fin.ext hb
      rw [ea, eb]
    have h3 : (I.frQ v)⁻¹ * bc (I.iw v) (gamMat sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p)
          (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) γ) * I.frQ v =
        bc (I.eQ v).symm.toRingHom ((I.fr (I.pl v).1 (I.pl v).2)⁻¹ *
          bc ((RingHom.fst _ _).comp (I.spl (I.pl v).1 (I.pl v).2).toRingHom)
            (bc (inclE (F := F) ((I.pl v).1.adicCompletion F)) (gamMat sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p)
              (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) γ)) * I.fr (I.pl v).1 (I.pl v).2) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    show I.eQ v _ = _
    rw [h2, h1, h3]
    show I.eQ v ((I.eQ v).symm _) = _
    rw [RingEquiv.apply_symm_apply]
    rfl

end Formalism.L2.G
