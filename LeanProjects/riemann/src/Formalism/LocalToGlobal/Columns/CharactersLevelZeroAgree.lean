import Formalism.LocalToGlobal.Columns.HermOwed

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem th_reGL_id {n : ℕ} (R : Type) [CommRing R] :
    (Formalism.L2.Forms.reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id (GL (Fin n) R) :=
  MonoidHom.ext fun x => Formalism.L2.Forms.reGL_rfl R x

theorem th_sameCar_refl {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {cls : Type} {stab : cls → Type} (Lb : Submodule (𝓞 E) (Fin n → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (y : cls → GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (st : ∀ c, stab c → GL (Fin n) E) :
    Formalism.L2.Forms.SameCar (rfl : n = n) Lb Lb Uloc Uloc U U y y st st where
  Lb_eq := (Formalism.L2.Forms.reL_rfl Lb).symm
  Uloc_eq := fun v => by rw [th_reGL_id, Subgroup.map_id]
  U_eq := by rw [th_reGL_id, Subgroup.map_id]
  y_eq := fun c => (Formalism.L2.Forms.reGL_rfl _ (y c)).symm
  st_eq := fun c s => (Formalism.L2.Forms.reGL_rfl _ (st c s)).symm

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem levPack_sameCar (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) :
    Formalism.L2.Forms.SameCar H.hn (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Lb
      (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Uloc (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Uloc
      (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.U (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.U
      (fun c => ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c).1) (fun c => ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).y c).1)
      (fun c t => ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.stabI c t).1)
      (fun c t => ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).stabI c t).1) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_sameCar_refl _ _ _ _ _

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)

theorem characters_level_zero_agree (u : d.what₂.Word) :
    Formalism.L2.Forms.SameCar (Formalism.L2.Forms.rank_eq_first_level d.R) ((hermCols a hS hP hK S hI).lev0 u).Lb (classAgreement a hS hH hP u 0 (Nat.zero_le _)).lev.Lb
      ((hermCols a hS hP hK S hI).lev0 u).Uloc (classAgreement a hS hH hP u 0 (Nat.zero_le _)).lev.Uloc
      ((hermCols a hS hP hK S hI).lev0 u).U (classAgreement a hS hH hP u 0 (Nat.zero_le _)).lev.U
      (fun c => (((hermCols a hS hP hK S hI).lev0 u).y c).1) (fun c => ((classAgreement a hS hH hP u 0 (Nat.zero_le _)).y c).1)
      (fun c t => (((hermCols a hS hP hK S hI).lev0 u).stabI c t).1)
      (fun c t => ((classAgreement a hS hH hP u 0 (Nat.zero_le _)).stabI c t).1) :=
  levPack_sameCar d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) _ _ _ _ (hK u 0) (hCrd0 hS u) (stepCrd a hS hH u 0 (Nat.zero_le _))

theorem th_carI (u : d.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ d.R.m) :
    Formalism.L2.Forms.SameCar (CF.rankN (d.colRec a) i hm) ((hermCols a hS hP hK S hI).lev u i h1 hm).Lb (classAgreement a hS hH hP u i hm).lev.Lb
      ((hermCols a hS hP hK S hI).lev u i h1 hm).Uloc (classAgreement a hS hH hP u i hm).lev.Uloc
      ((hermCols a hS hP hK S hI).lev u i h1 hm).U (classAgreement a hS hH hP u i hm).lev.U
      (fun c => (((hermCols a hS hP hK S hI).cls u i h1 hm).y c).1) (fun c => ((classAgreement a hS hH hP u i hm).y c).1)
      (fun c t => (((hermCols a hS hP hK S hI).cls u i h1 hm).stabI c t).1)
      (fun c t => ((classAgreement a hS hH hP u i hm).stabI c t).1) :=
  levPack_sameCar d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) _ _ _ _ (hK u i) (hCrd hS u i hm) (stepCrd a hS hH u i hm)

end Rec

section Pr

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem th_pr (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) (z' : ↥(CF.Ld D u i hi c))
    (h : z'.1 = CF.crdN D i hi z.1) : (P i hi).pr v c z' = hxPr A P i v c z := by
  rw [hxPr_eq A P i hi]
  congr 1
  exact Subtype.ext h

theorem th_prk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c))
    (z' : ↥(CF.Lk A i hi v c)) (h : z'.1 = CF.crdN D i hi z.1) : (P i hi).prk v c z' = hxPrk A P i v c z := by
  rw [hxPrk_eq A P i hi]
  congr 1
  exact Subtype.ext h

end Pr

end Formalism.L2.Col
