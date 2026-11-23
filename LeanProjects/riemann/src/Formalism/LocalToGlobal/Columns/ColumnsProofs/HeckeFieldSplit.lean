import Mathlib
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSCoef
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
import Formalism.LocalToGlobal.Divisibility.LiftLatInst

open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section FormBC

variable {X : Fields} {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L) {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

def hfsFormBC (F : CoefFrame ι) (C : CoefPk X n (DecoSet X.E n ST SG))
    (rho' : UF X.E n →* Module.End L (VV L C.lam)) (pair' : VV L C.lam →ₗ⋆[L] VV L C.lam →ₗ[L] L)
    (Nab' Del' : DecoSet X.E n ST SG → Submodule (𝓞 L) (VV L C.lam))
    (hrho : ∀ γ v, rho' γ (hfsJ ι C.lam v) = hfsJ ι C.lam (C.rho γ v)) (Λ : LevFam X.E X.K n SG) :
    GSDBC ι (formGSD C Λ) (formGSD (X := X.coefExt L ι) ⟨C.lam, rho', pair', Nab', Del'⟩ (Λ.coefMap ι)) where
  eG := MonoidHom.id _
  eG_surj g := ⟨g, rfl⟩
  eD := Equiv.refl _
  eD_smul _ _ := rfl
  j := hfsJ ι C.lam
  j_smul := hfsJ_smul ι C.lam
  li := hfsJ_li ι C.lam F
  sp := hfsJ_span ι C.lam F
  rho g v := by
    show (((Λ.coefMap ι).chr g.2 : Lˣ) : L) • rho' g.1 (hfsJ ι C.lam v) =
      hfsJ ι C.lam ((((Λ.chr g.2 : X.Kˣ)) : X.K) • C.rho g.1 v)
    have hc : (((Λ.coefMap ι).chr g.2 : Lˣ) : L) = ι (((Λ.chr g.2 : X.Kˣ)) : X.K) :=
      congrArg Units.val (LevFam.coefMap_chr ι Λ g.2)
    rw [hfsJ_smul, hrho, hc]

theorem hfs_nb (C : CoefPk X n (DecoSet X.E n ST SG)) (C' : CoefPk (X.coefExt L ι) n (DecoSet X.E n ST SG))
    (Λ : LevFam X.E X.K n SG) (Λ' : LevFam X.E L n SG) (P : Ideal (𝓞 X.E)) (i : ℕ) (d' : DecoSet X.E n ST SG) :
    ((formPts (X := X.coefExt L ι) C' Λ').nb P i d').map (Equiv.refl (DecoSet X.E n ST SG)).toEmbedding =
      (formPts C Λ).nb P i d' := by
  rw [show (Equiv.refl (DecoSet X.E n ST SG)).toEmbedding = Function.Embedding.refl _ from rfl,
    Finset.map_refl]
  rfl

theorem hfs_nbI (C : CoefPk X n (DecoSet X.E n ST SG)) (C' : CoefPk (X.coefExt L ι) n (DecoSet X.E n ST SG))
    (Λ : LevFam X.E X.K n SG) (Λ' : LevFam X.E L n SG) (P : Ideal (𝓞 X.E)) (s : List ℕ) (d' : DecoSet X.E n ST SG) :
    ((formPts (X := X.coefExt L ι) C' Λ').nbI P s d').map (Equiv.refl (DecoSet X.E n ST SG)).toEmbedding =
      (formPts C Λ).nbI P s d' := by
  rw [show (Equiv.refl (DecoSet X.E n ST SG)).toEmbedding = Function.Embedding.refl _ from rfl,
    Finset.map_refl]
  rfl

private theorem lifts_heckeD_of_nb_map {S : GSD X.K} {S' : GSD L} (b : GSDBC ι S S') (c : DecoPts S X.E n ST SG)
    (c' : DecoPts S' X.E n ST SG) (P : Ideal (𝓞 X.E)) (i : ℕ)
    (hnb : ∀ d', (c'.nb P i d').map b.eD.toEmbedding = c.nb P i (b.eD d')) :
    b.Lifts (heckeD c' P i).op (heckeD c P i).op := by
  intro φ
  apply Subtype.ext
  funext d'
  simp only [heckeD_op_apply, GSDBC.lift_apply, map_sum]
  rw [← hnb d', Finset.sum_map]
  rfl

private theorem lifts_heckeI_of_nbI_map {S : GSD X.K} {S' : GSD L} (b : GSDBC ι S S') (c : DecoPts S X.E n ST SG)
    (c' : DecoPts S' X.E n ST SG) (P : Ideal (𝓞 X.E)) (s : List ℕ)
    (hnb : ∀ d', (c'.nbI P s d').map b.eD.toEmbedding = c.nbI P s (b.eD d')) :
    b.Lifts (heckeI c' P s).op (heckeI c P s).op := by
  intro φ
  apply Subtype.ext
  funext d'
  simp only [heckeI_op_apply, GSDBC.lift_apply, map_sum]
  rw [← hnb d', Finset.sum_map]
  rfl

theorem hfs_splitAll_formPts (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) [FiniteDimensional X.K (formGSD C Λ).EqFun] (hc : HeckeCommAll (formPts C Λ) S0)
    {p : X.K[X]} (hp : HeckePolyFor (heckeFamAll (formPts C Λ) S0) p) (hsp : (p.map ι).Splits)
    (rho' : UF X.E n →* Module.End L (VV L C.lam)) (pair' : VV L C.lam →ₗ⋆[L] VV L C.lam →ₗ[L] L)
    (Nab' Del' : DecoSet X.E n ST SG → Submodule (𝓞 L) (VV L C.lam))
    (hrho : ∀ γ v, rho' γ (hfsJ ι C.lam v) = hfsJ ι C.lam (C.rho γ v)) :
    SplitOver (heckeFamAll (formPts (X := X.coefExt L ι) ⟨C.lam, rho', pair', Nab', Del'⟩ (Λ.coefMap ι)) S0) := by
  obtain ⟨F⟩ : Nonempty (CoefFrame ι) := CoefFrame.nonempty (ι := ι)
  refine (hfsFormBC ι F C rho' pair' Nab' Del' hrho Λ).splitOver F (heckeFamAll (formPts C Λ) S0) _ ?_ hc hp hsp
  intro x
  cases x with
  | inl x => exact lifts_heckeD_of_nb_map ι _ _ _ x.1.1.asIdeal x.2 (fun d' => hfs_nb ι C _ Λ _ x.1.1.asIdeal x.2 d')
  | inr x => exact lifts_heckeI_of_nbI_map ι _ _ _ x.1.1.asIdeal x.2 (fun d' => hfs_nbI ι C _ Λ _ x.1.1.asIdeal x.2 d')

theorem hfs_splitAll_sq_reidx {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (h : SG₁ = SG₂) (lam : X.Tau → DomWeight n)
    (Λ : LevFam X.E X.K n SG₂) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (hfd : FiniteDimensional X.K (formGSD (squarePk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv).EqFun)
    (hc : HeckeCommAll (formPts (squarePk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv) S0) {p : X.K[X]}
    (hp : HeckePolyFor (heckeFamAll (formPts (squarePk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv) S0) p)
    (hsp : (p.map ι).Splits) :
    SplitOver (heckeFamAll (formPts (X := X.coefExt L ι) (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N)
      ((Λ.coefMap ι).reidx h).inv) S0) := by
  subst h
  haveI := hfd
  have e : ((Λ.coefMap ι).reidx rfl).inv = Λ.inv.coefMap ι := LevFam.coefMap_inv (ι := ι) Λ
  rw [e]
  exact hfs_splitAll_formPts ι (squarePk X lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N) Λ.inv S0 hc hp hsp
    (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).rho
    (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).pair
    (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).Nab
    (squarePk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).Del
    (fun γ v => hfs_rhoV (ι := ι) (lam := lam) (emb := X.emb) (γ := ufGL X.E n γ) (v := v))

theorem hfs_splitAll_rd_reidx {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (h : SG₁ = SG₂) (lam : X.Tau → DomWeight n)
    (Λ : LevFam X.E X.K n SG₂) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (hfd : FiniteDimensional X.K (formGSD (roundPk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv).EqFun)
    (hc : HeckeCommAll (formPts (roundPk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv) S0) {p : X.K[X]}
    (hp : HeckePolyFor (heckeFamAll (formPts (roundPk X lam fun d : DecoSet X.E n ∅ SG₂ => d.1.N) Λ.inv) S0) p)
    (hsp : (p.map ι).Splits) :
    SplitOver (heckeFamAll (formPts (X := X.coefExt L ι) (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N)
      ((Λ.coefMap ι).reidx h).inv) S0) := by
  subst h
  haveI := hfd
  have e : ((Λ.coefMap ι).reidx rfl).inv = Λ.inv.coefMap ι := LevFam.coefMap_inv (ι := ι) Λ
  rw [e]
  exact hfs_splitAll_formPts ι (roundPk X lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N) Λ.inv S0 hc hp hsp
    (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).rho
    (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).pair
    (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).Nab
    (roundPk (X.coefExt L ι) lam fun d : DecoSet X.E n ∅ SG₁ => d.1.N).Del
    (fun γ v => hfs_rhoVr (ι := ι) (lam := lam) (emb := X.emb) (γ := ufGL X.E n γ) (v := v))

end FormBC

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)

end Rows

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

end Fam

end Formalism.L2.Col
