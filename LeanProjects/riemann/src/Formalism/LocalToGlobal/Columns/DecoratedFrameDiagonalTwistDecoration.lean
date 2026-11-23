import Formalism.LocalToGlobal.Columns.RecChainYUnfPol

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Fr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.SameOn (B : Finset (HeightOneSpectrum (𝓞 E))) (d d' : DecoSet E n ST SG) : Prop := ∀ P ∈ B, d'.1.at P = d.1.at P

theorem DecoSet.SameOn.smul {B : Finset (HeightOneSpectrum (𝓞 E))} {d d' : DecoSet E n ST SG} (h : DecoSet.SameOn B d d')
    (a : UF E n × GLG E n SG) : DecoSet.SameOn B (a • d) (a • d') := by
  intro P hP
  have e : localization₂ P.asIdeal d'.1.N = localization₂ P.asIdeal d.1.N := h P hP
  rw [DecoSet.smul_val, DecoSet.smul_val]
  ext x
  show x ∈ localization₂ P.asIdeal (gmap a.1.1 d'.1.N) ↔ x ∈ localization₂ P.asIdeal (gmap a.1.1 d.1.N)
  rw [mem_localization_gmap, mem_localization_gmap, e]

theorem DecoSet.SameOn.of_smul {B : Finset (HeightOneSpectrum (𝓞 E))} {d d' : DecoSet E n ST SG} (a : UF E n × GLG E n SG)
    (h : DecoSet.SameOn B (a • d) (a • d')) : DecoSet.SameOn B d d' := by
  have h2 := h.smul a⁻¹
  simpa only [inv_smul_smul] using h2

def DecoF.repl (p : DecoF E n ST SG Q) (d' : DecoSet E n ST SG) (h : DecoSet.SameOn Q p.deco d') : DecoF E n ST SG Q :=
  ⟨(d', p.1.2), fun P x => by rw [h P.1 P.2]; exact p.2 P x⟩

open Classical in

def DecoF.mv (p : DecoF E n ST SG Q) (d' : DecoSet E n ST SG) : DecoF E n ST SG Q :=
  if h : DecoSet.SameOn Q p.deco d' then p.repl d' h else p

theorem DecoF.mv_pos {p : DecoF E n ST SG Q} {d' : DecoSet E n ST SG} (h : DecoSet.SameOn Q p.deco d') : p.mv d' = p.repl d' h := by
  unfold DecoF.mv; rw [dif_pos h]

theorem DecoF.mv_neg {p : DecoF E n ST SG Q} {d' : DecoSet E n ST SG} (h : ¬ DecoSet.SameOn Q p.deco d') : p.mv d' = p := by
  unfold DecoF.mv; rw [dif_neg h]

theorem DecoF.mv_deco {p : DecoF E n ST SG Q} {d' : DecoSet E n ST SG} (h : DecoSet.SameOn Q p.deco d') : (p.mv d').deco = d' := by
  rw [DecoF.mv_pos h]; rfl

theorem DecoF.mv_fr (p : DecoF E n ST SG Q) (d' : DecoSet E n ST SG) (P : Q) : (p.mv d').fr P = p.fr P := by
  unfold DecoF.mv; split_ifs <;> rfl

theorem DecoF.smul_deco (g : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) : (g • p).deco = (g.1, g.2.1) • p.deco := rfl

theorem DecoF.mv_smul (g : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) (d' : DecoSet E n ST SG) :
    (g • p).mv ((g.1, g.2.1) • d') = g • p.mv d' := by
  by_cases h : DecoSet.SameOn Q p.deco d'
  · have h' : DecoSet.SameOn Q (g • p).deco ((g.1, g.2.1) • d') := by
      rw [DecoF.smul_deco]; exact h.smul _
    rw [DecoF.mv_pos h', DecoF.mv_pos h]
    apply Subtype.ext; apply Prod.ext
    · exact (DecoF.smul_deco g (p.repl d' h)).symm
    · rfl
  · have h' : ¬ DecoSet.SameOn Q (g • p).deco ((g.1, g.2.1) • d') := by
      rw [DecoF.smul_deco]; exact fun hh => h (DecoSet.SameOn.of_smul _ hh)
    rw [DecoF.mv_neg h', DecoF.mv_neg h]

theorem DecoSet.sameOn_diagonalTwist (B : Finset (HeightOneSpectrum (𝓞 E))) (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : DecoSet E n ST SG) :
    DecoSet.SameOn B d (d.dia1 P a) := fun _ _ => rfl

theorem DecoSet.sameOn_up {B : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet E n ST SG) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    (hB : ∀ P' ∈ B, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (q : 𝓞 E) {x : Sp E n} (hx : x ∈ d.1.N) : DecoSet.SameOn B d (d.up P q x) := by
  intro P' hP'
  unfold DecoSet.up
  split_ifs with hok
  · show localization₂ P'.asIdeal (upN P.1.asIdeal d.1.N x) = localization₂ P'.asIdeal d.1.N
    exact ((upN_spec d.2.lat d.2.uni P.1 hne hx).2.2.1 P' (hB P' hP').1 (hB P' hP').2).localization_eq
  · rfl

theorem DecoSet.sameOn_dn {B : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet E n ST SG) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    (hB : ∀ P' ∈ B, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet.SameOn B d (d.dn P f') := by
  intro P' hP'
  unfold DecoSet.dn
  split_ifs with hok
  · show localization₂ P'.asIdeal (d.1.dnN P) = localization₂ P'.asIdeal d.1.N
    exact ((d.2.dnN_spec P hne).2.2.1 P' (hB P' hP').1 (hB P' hP').2).localization_eq
  · rfl

def DecoF.dia1 (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (p : DecoF E n ST SG Q) : DecoF E n ST SG Q := ⟨(p.1.1.dia1 P a, p.1.2), p.2⟩

theorem DecoF.decoratedFrame_diagonalTwist_decoration (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (p : DecoF E n ST SG Q) : (p.dia1 P a).deco = p.deco.dia1 P a := rfl

theorem DecoF.decoratedFrame_diagonalTwist_frame (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (p : DecoF E n ST SG Q) (P' : Q) : (p.dia1 P a).fr P' = p.fr P' := rfl

theorem DecoF.decoratedFrame_diagonalTwist_eq_move (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (p : DecoF E n ST SG Q) : p.dia1 P a = p.mv (p.deco.dia1 P a) := by
  rw [DecoF.mv_pos (DecoSet.sameOn_diagonalTwist Q P a p.deco)]; rfl

theorem DecoF.decoratedFrame_diagonalTwist_smul (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (g : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) :
    (g • p).dia1 P a = g • p.dia1 P a := rfl

def DecoF.upL (p : DecoF E n ST SG Q) (P : ST) (q : 𝓞 E) (x : p.deco.lv P) : DecoF E n ST SG Q := p.mv (p.deco.upL P q x)

def DecoF.dnL (p : DecoF E n ST SG Q) (P : ST) (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (p.deco.lk P)) : DecoF E n ST SG Q := p.mv (p.deco.dnL P g)

theorem DecoF.upL_deco (p : DecoF E n ST SG Q) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) (hQ : ∀ P' ∈ Q, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (q : 𝓞 E)
    (x : p.deco.lv P) : (p.upL P q x).deco = p.deco.upL P q x := by
  exact DecoF.mv_deco (DecoSet.sameOn_up p.deco P hne hQ q (x := modP.rep x) (Quotient.out x).2)

theorem DecoF.dnL_deco (p : DecoF E n ST SG Q) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) (hQ : ∀ P' ∈ Q, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1)
    (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (p.deco.lk P)) : (p.dnL P g).deco = p.deco.dnL P g := by
  exact DecoF.mv_deco (DecoSet.sameOn_dn p.deco P hne hQ _)

theorem DecoF.upL_fr (p : DecoF E n ST SG Q) (P : ST) (q : 𝓞 E) (x : p.deco.lv P) (P' : Q) : (p.upL P q x).fr P' = p.fr P' := by
  exact DecoF.mv_fr p _ P'

theorem DecoF.dnL_fr (p : DecoF E n ST SG Q) (P : ST) (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (p.deco.lk P)) (P' : Q) :
    (p.dnL P g).fr P' = p.fr P' := by
  exact DecoF.mv_fr p _ P'

end Fr

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem locLat_sameAt {E : Type} [Field E] [NumberField E] {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 E))) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ P ∈ SB, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) (e : SB → ℤ) : locLat SB N' e = locLat SB N e := by
  unfold locLat
  exact iInf_congr fun P => by rw [h P.1 P.2]

theorem ybSet_sameAt {n : ℕ} {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : ∀ P ∈ rowSG Pr sel mu, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) :
    ybSet sel mu cst N' = ybSet sel mu cst N := by
  unfold ybSet
  rw [locLat_sameAt _ h, locLat_sameAt _ h]

end Yb

end Formalism.L2.Col
